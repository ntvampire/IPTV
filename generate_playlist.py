import gzip
import ipaddress
import json
import os
import re
import socket
import threading
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor, as_completed
from urllib.parse import urljoin, urlparse
import defusedxml.ElementTree as DefusedET
import requests

INPUT_CHANNELS_FILE = "input_channels.txt"
INPUT_LISTS_FILE = "input_lists.txt"
INPUT_FILE = INPUT_CHANNELS_FILE  # Backwards compatibility
OUTPUT_FILE = "index.m3u"
OUTPUT_EPG_FILE = "epg.xml.gz"
LOGOS_DIR = "logos"

# Upstream EPG sources in order of priority
PRIMARY_EPG_URL = "https://iptvx.one/epg/epg.xml.gz"
SECONDARY_EPG_URL = "https://epg.one/epg2.xml.gz"

# Safety and resource limits
MAX_M3U_BYTES = 10 * 1024 * 1024      # 10 MB max for external M3U playlists
MAX_EPG_GZ_BYTES = 100 * 1024 * 1024  # 100 MB max for compressed XMLTV download
MAX_EPG_XML_BYTES = 512 * 1024 * 1024 # 512 MB max uncompressed XML stream
MAX_REDIRECTS = 5
ALLOWED_EXTHTTP_HEADERS = {"user-agent", "referer", "origin"}

# GitHub Pages base URL configuration
GITHUB_REPOSITORY = os.getenv("GITHUB_REPOSITORY", "ntvampire/IPTV")
REPO_OWNER, REPO_NAME = (
    GITHUB_REPOSITORY.split("/")
    if "/" in GITHUB_REPOSITORY
    else ("ntvampire", "iptv")
)
BASE_PAGES_LOGOS_URL = f"https://{REPO_OWNER}.github.io/{REPO_NAME}/logos"
CUSTOM_EPG_URL = f"https://{REPO_OWNER}.github.io/{REPO_NAME}/epg.xml.gz"

HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
    "Accept": "*/*",
}

IGNORED_CHANNEL_NAMES = {
    # Original promo & info entries
    "loganettv all",
    "telegram - t.me/loganettv_original",
    "telegram - @loganettv_original",
    "loganettv",
    "iptvru",
    # Teleshopping / promo channels
    "shopping live",
    "ювелирочка",
    "shop & show",
    "leomax",
    "витрина тв",
    # Unwanted generic streams or duplicates
    "беларусь",
    "бст",
    "ctv.by",
    "крым",
    "москва",
    "новгород",
    "севастополь",
    "екатеринбург",
    "приднестровье",
    "mezzo",
    "майдан",
    "курай",
    "матур",
    "пинск тв",
    "юганск",
    "euronews",
    "rt english",
    "кубань",
    "татарстан",
    "тест",
    "сити эдем",
    "deutsche welle",
    "соловьев",
    "maidan",
    "stingray",
    "лдпр",
    "инфоканал",
}

EXCLUDED_EXTERNAL_GROUPS = {
    "релакс",
    "медитативные",
    "relax",
    "религия",
    "христианские",
    "религиозные",
    "православные",
    "religion",
    "местные",
    "региональные",
}

CATEGORY_ORDER = [
    "Общие",
    "Кино и сериалы",
    "Детские",
    "Музыка",
    "Развлекательные",
    "Познавательные",
    "Спорт",
    "Новости",
]
CATEGORY_INDEX_MAP = {cat: idx for idx, cat in enumerate(CATEGORY_ORDER)}

# Force-override channel groups by channel name (lowercase)
CHANNEL_GROUP_OVERRIDES = {
    "trace sport stars": "Спорт",
    "trace sport stars hd": "Спорт",
}

GROUP_NORMALIZATION = {
    "кино": "Кино и сериалы",
    "фильмы": "Кино и сериалы",
    "сериалы": "Кино и сериалы",
    "cinema": "Кино и сериалы",
    "movies": "Кино и сериалы",
    "кино и сериалы (российские)": "Кино и сериалы",
    "спорт": "Спорт",
    "спортивные": "Спорт",
    "sports": "Спорт",
    "sport": "Спорт",
    "музыка": "Музыка",
    "музыкальные": "Музыка",
    "music": "Музыка",
    "детские": "Детские",
    "дети": "Детские",
    "мультфильмы": "Детские",
    "kids": "Детские",
    "детям": "Детские",
    "новости": "Новости",
    "новостные": "Новости",
    "информационные": "Новости",
    "news": "Новости",
    "познавательные": "Познавательные",
    "знания": "Познавательные",
    "культура": "Познавательные",
    "образовательные": "Познавательные",
    "наука": "Познавательные",
    "документальные": "Познавательные",
    "discovery": "Познавательные",
    "nature": "Познавательные",
    "общие": "Общие",
    "общественные": "Общие",
    "эфирные": "Общие",
    "федеральные": "Общие",
    "центральные": "Общие",
    "развлекательные": "Развлекательные",
    "развлекательные (местные)": "Развлекательные",
    "развлечение": "Развлекательные",
    "юмор": "Развлекательные",
    "хобби и увлечения": "Развлекательные",
    "хобби": "Развлекательные",
}


SHORT_IGNORED_TOKENS = {"эро", "sex", "xxx", "бст", "лдпр", "тест"}
_SHORT_IGNORED_PATTERNS = [
    re.compile(rf"(?:^|[^\w]){re.escape(tok)}(?:$|[^\w])", re.IGNORECASE)
    for tok in SHORT_IGNORED_TOKENS
]


def is_blacklisted(channel_name):
    """Check if channel name matches blacklisted phrases or standalone short tokens."""
    clean = channel_name.strip().lower()
    if any(pat.search(clean) for pat in _SHORT_IGNORED_PATTERNS):
        return True
    return any(
        ignored in clean
        for ignored in IGNORED_CHANNEL_NAMES
        if ignored not in SHORT_IGNORED_TOKENS
    )


def normalize_group(group_title):
    if not group_title:
        return "Общие"
    clean = group_title.strip().lower()
    if clean in GROUP_NORMALIZATION:
        return GROUP_NORMALIZATION[clean]
    base_clean = re.sub(r"[\(\[\{].*?[\)\]\}]", "", clean).strip()
    if base_clean in GROUP_NORMALIZATION:
        return GROUP_NORMALIZATION[base_clean]
    return group_title.strip().capitalize()


_CACHED_LOCAL_LOGOS = None
_THREAD_LOCAL = threading.local()


def _get_session():
    """Return a thread-local requests.Session for connection pooling."""
    if not hasattr(_THREAD_LOCAL, "session"):
        _THREAD_LOCAL.session = requests.Session()
    return _THREAD_LOCAL.session


def is_safe_public_url(url):
    """Validate that URL uses http/https and resolves only to global public IP addresses."""
    try:
        parsed = urlparse(url)
    except Exception:
        return False

    if parsed.scheme not in ("http", "https") or not parsed.hostname:
        return False

    hostname = parsed.hostname
    try:
        addr_info = socket.getaddrinfo(hostname, None)
    except OSError:
        return False

    if not addr_info:
        return False

    for info in addr_info:
        ip_str = info[4][0].split("%", 1)[0]
        try:
            ip = ipaddress.ip_address(ip_str)
            if isinstance(ip, ipaddress.IPv6Address) and ip.ipv4_mapped:
                ip = ip.ipv4_mapped
        except ValueError:
            return False

        if (
            not ip.is_global
            or ip.is_private
            or ip.is_loopback
            or ip.is_link_local
            or ip.is_multicast
            or ip.is_reserved
            or ip.is_unspecified
        ):
            return False

    return True


def _safe_request(method, url, headers=None, timeout=4, stream=False):
    """Execute HTTP request with SSRF validation on initial URL and every redirect hop."""
    session = _get_session()
    current_url = url
    req_method = method

    for _ in range(MAX_REDIRECTS + 1):
        if not is_safe_public_url(current_url):
            return None

        res = session.request(
            req_method,
            current_url,
            headers=headers,
            timeout=timeout,
            allow_redirects=False,
            stream=stream,
        )
        if res.status_code in (301, 302, 303, 307, 308):
            location = res.headers.get("Location")
            res.close()
            if not location:
                return None
            current_url = urljoin(current_url, location)
            if res.status_code == 303 and req_method == "HEAD":
                req_method = "GET"
            continue
        return res

    return None


def _extract_stream_headers(vlc_opts, http_opts=None):
    """Extract sanitized HTTP headers dict from #EXTVLCOPT and #EXTHTTP directives."""
    headers_dict = {}
    extra_vlc_opts = []

    for opt in vlc_opts or []:
        clean_opt = opt.replace("\r", "").replace("\n", "").strip()
        if "http-user-agent=" in clean_opt:
            val = clean_opt.split("http-user-agent=", 1)[1].strip()
            if val:
                headers_dict["User-Agent"] = val
        elif "http-referrer=" in clean_opt:
            val = clean_opt.split("http-referrer=", 1)[1].strip()
            if val:
                headers_dict["Referer"] = val
        elif "http-origin=" in clean_opt:
            val = clean_opt.split("http-origin=", 1)[1].strip()
            if val:
                headers_dict["Origin"] = val
        elif clean_opt:
            extra_vlc_opts.append(clean_opt)

    for opt in http_opts or []:
        clean_opt = opt.replace("\r", "").replace("\n", "").strip()
        if not clean_opt.startswith("#EXTHTTP:"):
            continue
        try:
            payload = json.loads(clean_opt.split("#EXTHTTP:", 1)[1].strip())
        except Exception:
            continue
        if not isinstance(payload, dict):
            continue
        for k, v in payload.items():
            if not isinstance(k, str) or not isinstance(v, (str, int, float)):
                continue
            k_lower = k.strip().lower()
            if k_lower in ALLOWED_EXTHTTP_HEADERS:
                canonical = {"user-agent": "User-Agent", "referer": "Referer", "origin": "Origin"}[k_lower]
                clean_val = str(v).replace("\r", "").replace("\n", "").strip()
                if clean_val:
                    headers_dict[canonical] = clean_val

    return headers_dict, extra_vlc_opts


def get_local_logo_files():
    global _CACHED_LOCAL_LOGOS
    if _CACHED_LOCAL_LOGOS is None:
        if os.path.exists(LOGOS_DIR):
            _CACHED_LOCAL_LOGOS = [
                f for f in os.listdir(LOGOS_DIR) if f.lower().endswith(".png")
            ]
        else:
            _CACHED_LOCAL_LOGOS = []
    return _CACHED_LOCAL_LOGOS


def _is_html_content_type(res):
    ctype = (res.headers.get("Content-Type") or "").lower()
    return "text/html" in ctype or "application/xhtml" in ctype


def _is_valid_stream_sample(sample, url):
    stripped = sample.lstrip()[:32].lower()
    if stripped.startswith((b"<!doctype", b"<html")):
        return False
    if ".m3u8" in urlparse(url).path.lower() and b"#EXTM3U" not in sample.upper():
        return False
    return True


def check_stream(channel, timeout=4):
    """Probe primary and backup stream URLs safely and select the first live stream."""
    urls_to_test = [channel["url"]] + channel.get("backup_urls", [])
    url_vlc_opts = channel.get("url_vlc_opts", {})
    url_http_opts = channel.get("url_http_opts", {})
    url_catchup_attrs = channel.get("url_catchup_attrs", {})
    url_audio_track = channel.get("url_audio_track", {})

    for u in urls_to_test:
        opts = url_vlc_opts.get(u, channel.get("vlc_opts", []))
        h_opts = url_http_opts.get(u, channel.get("http_opts", []))
        c_attrs = url_catchup_attrs.get(u, channel.get("catchup_attrs", {}))
        a_track = url_audio_track.get(u, channel.get("audio_track", ""))

        req_headers = dict(HEADERS)
        stream_headers, _ = _extract_stream_headers(opts, h_opts)
        req_headers.update(stream_headers)

        try:
            res = _safe_request("HEAD", u, headers=req_headers, timeout=timeout)
            if res is not None:
                try:
                    if res.status_code == 200 and not _is_html_content_type(res):
                        channel["url"] = u
                        channel["vlc_opts"] = opts
                        channel["http_opts"] = h_opts
                        channel["catchup_attrs"] = c_attrs
                        channel["audio_track"] = a_track
                        return channel
                finally:
                    res.close()

            res = _safe_request(
                "GET", u, headers=req_headers, timeout=timeout, stream=True
            )
            if res is not None:
                try:
                    if res.status_code in (200, 206) and not _is_html_content_type(res):
                        sample = b""
                        for chunk in res.iter_content(chunk_size=512):
                            if chunk:
                                sample = chunk[:512]
                                break
                        if _is_valid_stream_sample(sample, u):
                            channel["url"] = u
                            channel["vlc_opts"] = opts
                            channel["http_opts"] = h_opts
                            channel["catchup_attrs"] = c_attrs
                            channel["audio_track"] = a_track
                            return channel
                finally:
                    res.close()
        except Exception:
            pass
    return None


def find_local_logo(channel_name, tvg_id):
    files = get_local_logo_files()
    if not files:
        return ""

    candidates = [
        tvg_id.lower().strip(),
        re.sub(r"[^\w]+", "-", channel_name.lower()).strip("-"),
        re.sub(r"[^\w]+", "_", channel_name.lower()).strip("_"),
        re.sub(r"[^\w]+", "", channel_name.lower()),
        re.sub(r"[^\w]+", "-", tvg_id.lower()).strip("-"),
        re.sub(r"[^\w]+", "_", tvg_id.lower()).strip("_"),
    ]

    for cand in candidates:
        if not cand:
            continue
        for f in files:
            name_no_ext = os.path.splitext(f)[0].lower()
            if name_no_ext == cand:
                return f"{BASE_PAGES_LOGOS_URL}/{f}"

    for cand in candidates:
        if not cand:
            continue
        for f in files:
            name_no_ext = os.path.splitext(f)[0].lower()
            if cand in name_no_ext:
                return f"{BASE_PAGES_LOGOS_URL}/{f}"

    return ""


def load_manual_channels():
    channels = []
    if not os.path.exists(INPUT_FILE):
        return channels

    print("[*] Processing manual channels with local logos from logos/...")
    with open(INPUT_FILE, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = [p.strip() for p in line.split("|")]
            if len(parts) >= 3:
                name = parts[0]
                group = normalize_group(parts[1])
                url = parts[2]
                raw_tvg_id = parts[3] if len(parts) >= 4 and parts[3] else name

                logo_url = find_local_logo(name, raw_tvg_id)

                channels.append(
                    {
                        "name": name,
                        "group": group,
                        "url": url,
                        "logo": logo_url or "",
                        "tvg_id": raw_tvg_id,
                        "audio_track": "",
                        "vlc_opts": [],
                        "http_opts": [],
                        "catchup_attrs": {},
                        "is_manual": True,
                    }
                )
    return channels


def split_extinf_meta(extinf_line):
    """Split '#EXTINF:attrs,Channel Name' at the first comma outside quotes."""
    in_quote = None
    for idx, ch in enumerate(extinf_line):
        if ch in ('"', "'"):
            if in_quote is None:
                in_quote = ch
            elif in_quote == ch:
                in_quote = None
        elif ch == "," and in_quote is None:
            return extinf_line[:idx], extinf_line[idx + 1 :].strip()
    return extinf_line, "Unknown"


def sanitize_m3u_attr(value):
    """Sanitize attribute values to avoid broken quotes or injected newlines in #EXTINF."""
    return str(value).replace("\r", " ").replace("\n", " ").replace('"', "'").strip()


def _fetch_m3u_text(source_url):
    """Download an external M3U playlist safely within MAX_M3U_BYTES and decode as UTF-8."""
    res = _safe_request("GET", source_url, headers=HEADERS, timeout=15, stream=True)
    if res is None:
        return None
    try:
        if res.status_code != 200:
            return None
        chunks = []
        total = 0
        for chunk in res.iter_content(chunk_size=65536):
            if not chunk:
                continue
            total += len(chunk)
            if total > MAX_M3U_BYTES:
                print(f"[-] Playlist {source_url} exceeds {MAX_M3U_BYTES} byte limit, skipping.")
                return None
            chunks.append(chunk)
        raw_bytes = b"".join(chunks)
        ctype = (res.headers.get("Content-Type") or "").lower()
        if "charset=" in ctype and res.encoding:
            return raw_bytes.decode(res.encoding, errors="replace")
        try:
            return raw_bytes.decode("utf-8-sig")
        except UnicodeDecodeError:
            return raw_bytes.decode("cp1251", errors="replace")
    finally:
        res.close()


def parse_m3u_stream(source_url, source_name):
    """Fetch and parse channels, headers, and catchup attributes from an external M3U playlist."""
    channels = []
    print(f"[*] Fetching external playlist: {source_name} ...")
    try:
        text = _fetch_m3u_text(source_url)
        if not text:
            return channels

        lines = text.splitlines()
        current_meta = None
        current_vlc_opts = []
        current_http_opts = []

        for line in lines:
            line = line.strip()
            if not line:
                continue
            if line.startswith("#EXTINF:"):
                current_meta = line
                current_vlc_opts = []
                current_http_opts = []
            elif line.startswith("#EXTVLCOPT:"):
                current_vlc_opts.append(line.replace("\r", "").replace("\n", ""))
            elif line.startswith("#EXTHTTP:"):
                current_http_opts.append(line.replace("\r", "").replace("\n", ""))
            elif (
                urlparse(line).scheme in ("http", "https")
            ) and current_meta:
                attr_part, raw_name = split_extinf_meta(current_meta)
                name = raw_name.replace("\r", " ").replace("\n", " ").strip() or "Unknown"

                if is_blacklisted(name):
                    current_meta = None
                    current_vlc_opts = []
                    current_http_opts = []
                    continue

                group_match = re.search(
                    r'group-title="([^"]*)"', attr_part, re.IGNORECASE
                )
                raw_group = group_match.group(1).strip() if group_match else "Общие"

                if raw_group.lower() in EXCLUDED_EXTERNAL_GROUPS:
                    current_meta = None
                    current_vlc_opts = []
                    current_http_opts = []
                    continue

                group = normalize_group(raw_group)

                clean_name = name.strip().lower()
                if clean_name in CHANNEL_GROUP_OVERRIDES:
                    group = CHANNEL_GROUP_OVERRIDES[clean_name]

                logo_match = re.search(
                    r'tvg-logo="([^"]*)"', attr_part, re.IGNORECASE
                )
                logo = logo_match.group(1).strip() if logo_match else ""
                if logo and urlparse(logo).scheme not in ("http", "https"):
                    logo = ""

                tvg_id_match = re.search(
                    r'tvg-id="([^"]*)"', attr_part, re.IGNORECASE
                )
                tvg_id = tvg_id_match.group(1).strip() if tvg_id_match else name

                # Extract audio-track
                audio_track_match = re.search(
                    r'audio-track="([^"]*)"', attr_part, re.IGNORECASE
                )
                audio_track = (
                    audio_track_match.group(1).strip() if audio_track_match else ""
                )

                # Extract catchup/archive-related attributes
                catchup_attrs = {}
                for m in re.finditer(
                    r'([a-zA-Z0-9_\-]+)=(?:"([^"]*)"|\'([^\']*)\'|([^\s,]+))',
                    attr_part,
                ):
                    attr_name = m.group(1).lower()
                    attr_val = m.group(2) or m.group(3) or m.group(4) or ""
                    if (
                        attr_name.startswith("catchup")
                        or attr_name.startswith("arc-")
                        or "timeshift" in attr_name
                    ):
                        catchup_attrs[attr_name] = attr_val

                channels.append(
                    {
                        "name": name,
                        "group": group,
                        "url": line,
                        "logo": logo,
                        "tvg_id": tvg_id,
                        "audio_track": audio_track,
                        "vlc_opts": list(current_vlc_opts),
                        "http_opts": list(current_http_opts),
                        "catchup_attrs": dict(catchup_attrs),
                        "is_manual": False,
                    }
                )
                current_meta = None
                current_vlc_opts = []
                current_http_opts = []
    except Exception as e:
        print(f"[-] Error parsing {source_name}: {e}")
    return channels


def load_external_playlist_sources():
    sources = []
    if not os.path.exists(INPUT_LISTS_FILE):
        print(f"[!] Warning: {INPUT_LISTS_FILE} not found. Skipping external playlists.")
        return sources

    print(f"[*] Loading external playlist sources from {INPUT_LISTS_FILE}...")
    with open(INPUT_LISTS_FILE, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = [p.strip() for p in line.split("|")]
            if len(parts) >= 2:
                name = parts[0]
                url = parts[1]
            else:
                url = parts[0]
                name = url.split("/")[-1].split("?")[0] or "External"
            sources.append((name, url))
    return sources


def merge_external_playlists(playlist_sources):
    """
    Merges channels from multiple external playlists in priority order.
    playlist_sources: list of (source_name, channels_list)
    The earlier a playlist is in playlist_sources, the higher its priority.
    Subsequent playlists provide backup URLs and additional unique channels.
    """
    merged = {}
    for source_name, channels in playlist_sources:
        for ch in channels:
            key = ch["name"].strip().lower()
            if key not in merged:
                merged[key] = dict(ch)
                merged[key]["backup_urls"] = []
                merged[key]["url_vlc_opts"] = {ch["url"]: ch.get("vlc_opts", [])}
                merged[key]["url_http_opts"] = {ch["url"]: ch.get("http_opts", [])}
                merged[key]["url_catchup_attrs"] = {
                    ch["url"]: ch.get("catchup_attrs", {})
                }
                merged[key]["url_audio_track"] = {ch["url"]: ch.get("audio_track", "")}
            else:
                backup_url = ch.get("url")
                if (
                    backup_url
                    and backup_url != merged[key]["url"]
                    and backup_url not in merged[key]["backup_urls"]
                ):
                    merged[key]["backup_urls"].append(backup_url)
                    for map_key, field_key, default_val in (
                        ("url_vlc_opts", "vlc_opts", []),
                        ("url_http_opts", "http_opts", []),
                        ("url_catchup_attrs", "catchup_attrs", {}),
                        ("url_audio_track", "audio_track", ""),
                    ):
                        if map_key not in merged[key]:
                            merged[key][map_key] = {
                                merged[key]["url"]: merged[key].get(field_key, default_val)
                            }
                        merged[key][map_key][backup_url] = ch.get(field_key, default_val)

    return list(merged.values())


def filter_alive_channels(channels, max_workers=30):
    print(f"[*] Checking {len(channels)} external streams for availability...")
    alive_channels = []
    total = len(channels)
    done_count = 0

    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        future_to_channel = {executor.submit(check_stream, ch): ch for ch in channels}
        for future in as_completed(future_to_channel):
            done_count += 1
            res = future.result()
            if res:
                alive_channels.append(res)
            if done_count % 50 == 0 or done_count == total:
                print(f"  > Checked: {done_count}/{total} | Alive: {len(alive_channels)}")

    return alive_channels


class _BoundedStreamReader:
    """File-like wrapper enforcing a strict limit on decompressed bytes read."""

    def __init__(self, raw_stream, max_bytes):
        self._stream = raw_stream
        self._max_bytes = max_bytes
        self._bytes_read = 0

    def read(self, size=-1):
        data = self._stream.read(size)
        self._bytes_read += len(data)
        if self._bytes_read > self._max_bytes:
            raise ValueError(
                f"Decompressed XML stream exceeds {self._max_bytes} byte limit"
            )
        return data


def _create_empty_epg():
    """Fallback generator to guarantee epg.xml.gz exists when no prior file exists."""
    root = ET.Element("tv")
    tree = ET.ElementTree(root)
    tmp_path = f"{OUTPUT_EPG_FILE}.tmp"
    with gzip.open(tmp_path, "wb") as f:
        tree.write(f, encoding="utf-8", xml_declaration=True)
    os.replace(tmp_path, OUTPUT_EPG_FILE)


def _download_stream(url, target_path):
    """Downloads a gzipped stream safely within MAX_EPG_GZ_BYTES to target file path."""
    res = _safe_request("GET", url, headers=HEADERS, timeout=120, stream=True)
    if res is None:
        print(f"[-] Blocked or unreachable EPG URL: {url}")
        return False
    try:
        if res.status_code != 200:
            print(f"[-] Failed to fetch {url}, HTTP {res.status_code}")
            return False
        total = 0
        with open(target_path, "wb") as f:
            for chunk in res.iter_content(chunk_size=1024 * 512):
                if not chunk:
                    continue
                total += len(chunk)
                if total > MAX_EPG_GZ_BYTES:
                    print(f"[-] EPG stream {url} exceeds {MAX_EPG_GZ_BYTES} byte limit.")
                    return False
                f.write(chunk)
        return True
    finally:
        res.close()


def _normalize_epg_name(name):
    """Return (raw_lower, clean_no_archive, no_quality_suffix) forms for channel matching."""
    raw = name.strip().lower()
    clean = re.sub(r"\s*\(архив\)\s*", "", raw).strip()
    no_hd = re.sub(r"\s+(hd|fhd|4k|sd)$", "", clean).strip()
    return raw, clean, no_hd


def generate_custom_epg(channels):
    """Download and merge multiple upstream EPGs with iptvx.one priority.
    Complies strictly with XMLTV DTD: all <channel> elements precede <programme> elements.
    Secondary EPG programmes are only used as fallback if Primary has no programmes for the channel.
    Auto-resolves missing tvg-id and fallback tvg-logo icons from matched EPG entries.
    """
    target_ids = set()
    for ch in channels:
        if ch.get("tvg_id"):
            target_ids.add(ch["tvg_id"].strip().lower())
        if ch.get("name"):
            target_ids.update(_normalize_epg_name(ch["name"]))

    channel_elements = []
    programme_elements = []
    seen_channels = set()
    primary_channels_with_programmes = set()
    secondary_channels_with_programmes = set()
    epg_exact_name_to_id = {}
    epg_norm_name_to_id = {}
    epg_id_to_icon = {}

    sources = [
        ("iptvx.one (Primary)", PRIMARY_EPG_URL, True),
        ("epg.one (Secondary)", SECONDARY_EPG_URL, False),
    ]

    for source_name, source_url, is_primary in sources:
        temp_gz = f"temp_{re.sub(r'[^a-zA-Z0-9]', '_', source_name)}.xml.gz"
        print(f"[*] Downloading EPG stream from {source_name}: {source_url} ...")

        if not _download_stream(source_url, temp_gz):
            if os.path.exists(temp_gz):
                os.remove(temp_gz)
            continue

        print(f"[*] Filtering and merging from {source_name}...")
        kept_ch = 0
        kept_prog = 0

        try:
            with gzip.open(temp_gz, "rb") as gz_in:
                bounded_in = _BoundedStreamReader(gz_in, MAX_EPG_XML_BYTES)
                context = DefusedET.iterparse(bounded_in, events=("start", "end"))
                _, root = next(context)
                for event, elem in context:
                    if event != "end":
                        continue

                    if elem.tag == "channel":
                        ch_id = elem.get("id", "").strip()
                        ch_id_lower = ch_id.lower()
                        display_name_elem = elem.find("display-name")
                        display_text = (
                            display_name_elem.text
                            if display_name_elem is not None and display_name_elem.text
                            else ""
                        )
                        display_name, disp_clean, disp_no_hd = _normalize_epg_name(
                            display_text
                        )

                        if (
                            ch_id_lower in target_ids
                            or display_name in target_ids
                            or disp_clean in target_ids
                            or disp_no_hd in target_ids
                        ):
                            if ch_id_lower not in seen_channels:
                                channel_elements.append(elem)
                                seen_channels.add(ch_id_lower)
                                kept_ch += 1
                                if display_name and display_name not in epg_exact_name_to_id:
                                    epg_exact_name_to_id[display_name] = ch_id
                                if disp_clean and disp_clean not in epg_exact_name_to_id:
                                    epg_exact_name_to_id[disp_clean] = ch_id
                                if disp_no_hd and disp_no_hd not in epg_norm_name_to_id:
                                    epg_norm_name_to_id[disp_no_hd] = ch_id

                                icon_elem = elem.find("icon")
                                if icon_elem is not None:
                                    icon_src = (icon_elem.get("src") or "").strip()
                                    if urlparse(icon_src).scheme in ("http", "https"):
                                        epg_id_to_icon[ch_id_lower] = icon_src
                            else:
                                elem.clear()
                        else:
                            elem.clear()

                    elif elem.tag == "programme":
                        prog_ch = elem.get("channel", "").strip()
                        prog_ch_lower = prog_ch.lower()

                        if prog_ch_lower in seen_channels or prog_ch_lower in target_ids:
                            if is_primary:
                                programme_elements.append(elem)
                                primary_channels_with_programmes.add(prog_ch_lower)
                                kept_prog += 1
                            elif prog_ch_lower not in primary_channels_with_programmes:
                                programme_elements.append(elem)
                                secondary_channels_with_programmes.add(prog_ch_lower)
                                kept_prog += 1
                            else:
                                elem.clear()
                        else:
                            elem.clear()

                    root.clear()

            print(
                f"[+] {source_name}: added {kept_ch} new channels and {kept_prog} programmes."
            )

        except Exception as e:
            print(f"[-] Parsing error for {source_name}: {e}")
        finally:
            if os.path.exists(temp_gz):
                os.remove(temp_gz)

    channels_with_programmes = (
        primary_channels_with_programmes | secondary_channels_with_programmes
    )

    # Auto-resolve canonical tvg_id (exact match priority over HD-stripped) and fallback icon
    resolved_count = 0
    icon_count = 0
    for ch in channels:
        current_id = (ch.get("tvg_id") or "").strip()
        if current_id.lower() not in channels_with_programmes:
            name_raw, name_clean, name_no_hd = _normalize_epg_name(ch["name"])
            candidates = [
                epg_exact_name_to_id.get(name_raw),
                epg_exact_name_to_id.get(name_clean),
                epg_norm_name_to_id.get(name_no_hd),
            ]
            for candidate_id in candidates:
                if candidate_id and candidate_id.lower() in channels_with_programmes:
                    ch["tvg_id"] = candidate_id
                    resolved_count += 1
                    break

        if not ch.get("logo"):
            resolved_lower = (ch.get("tvg_id") or "").strip().lower()
            epg_icon = epg_id_to_icon.get(resolved_lower)
            if epg_icon:
                ch["logo"] = epg_icon
                icon_count += 1

    if resolved_count:
        print(
            f"[+] Auto-resolved canonical tvg-id for {resolved_count} channels from EPG."
        )
    if icon_count:
        print(f"[+] Populated fallback EPG logos for {icon_count} channels.")

    if channel_elements or programme_elements:
        new_root = ET.Element("tv", {"generator-info-name": "Custom Merged IPTV EPG"})
        # XMLTV DTD requires all channels before programmes: <!ELEMENT tv (channel*, programme*)>
        for ch_elem in channel_elements:
            new_root.append(ch_elem)
        for prog_elem in programme_elements:
            new_root.append(prog_elem)

        tree = ET.ElementTree(new_root)
        tmp_epg = f"{OUTPUT_EPG_FILE}.tmp"
        with gzip.open(tmp_epg, "wb") as f_out:
            tree.write(f_out, encoding="utf-8", xml_declaration=True)
        os.replace(tmp_epg, OUTPUT_EPG_FILE)
        print(
            f"[+] Successfully generated merged {OUTPUT_EPG_FILE} ({os.path.getsize(OUTPUT_EPG_FILE) // 1024} KB)"
        )
    elif os.path.exists(OUTPUT_EPG_FILE) and os.path.getsize(OUTPUT_EPG_FILE) > 100:
        print(
            f"[!] Warning: upstream EPGs produced no data, keeping existing {OUTPUT_EPG_FILE}."
        )
    else:
        _create_empty_epg()


def format_catchup_attrs(catchup_attrs):
    """Format sanitized catchup/archive attributes in canonical order."""
    if not catchup_attrs:
        return ""
    preferred_order = [
        "catchup",
        "catchup-days",
        "catchup-source",
        "catchup-type",
        "catchup-time",
        "timeshift",
        "arc-type",
        "arc-time",
    ]
    parts = []
    seen = set()
    for key in preferred_order:
        if key in catchup_attrs:
            clean_key = re.sub(r"[^a-zA-Z0-9_\-]", "", key)
            parts.append(f'{clean_key}="{sanitize_m3u_attr(catchup_attrs[key])}"')
            seen.add(key)
    for key, val in catchup_attrs.items():
        if key not in seen:
            clean_key = re.sub(r"[^a-zA-Z0-9_\-]", "", key)
            if clean_key:
                parts.append(f'{clean_key}="{sanitize_m3u_attr(val)}"')
    return " " + " ".join(parts) if parts else ""


def format_channel_headers(vlc_opts, http_opts=None):
    """Return unified #EXTVLCOPT and #EXTHTTP header lines for cross-player compatibility."""
    headers_dict, extra_vlc_opts = _extract_stream_headers(vlc_opts, http_opts)
    lines = []

    vlc_key_map = {
        "User-Agent": "http-user-agent",
        "Referer": "http-referrer",
        "Origin": "http-origin",
    }
    for header_name, vlc_key in vlc_key_map.items():
        if header_name in headers_dict:
            lines.append(f"#EXTVLCOPT:{vlc_key}={headers_dict[header_name]}")

    for opt in extra_vlc_opts:
        if opt not in lines:
            lines.append(opt)

    if headers_dict:
        lines.append(f"#EXTHTTP:{json.dumps(headers_dict, ensure_ascii=False)}")

    return lines


def main():
    manual_channels = load_manual_channels()

    external_sources = load_external_playlist_sources()
    all_external_lists = []
    for source_name, source_url in external_sources:
        channels = parse_m3u_stream(source_url, source_name)
        if channels:
            all_external_lists.append((source_name, channels))

    external_channels = merge_external_playlists(all_external_lists)

    manual_keys = {ch["name"].strip().lower() for ch in manual_channels}
    filtered_external = [
        ch
        for ch in external_channels
        if ch["name"].strip().lower() not in manual_keys
    ]

    print(f"[*] Verifying manual streams ({len(manual_channels)} channels)...")
    alive_manual = []
    for ch in manual_channels:
        res = check_stream(ch, timeout=8)
        if not res:
            res = check_stream(ch, timeout=8)
        if res:
            alive_manual.append(res)
        else:
            print(f"[!] Warning: manual channel '{ch['name']}' not responding, keeping in playlist anyway.")
            alive_manual.append(ch)

    alive_external = filter_alive_channels(filtered_external, max_workers=30)

    final_list = alive_manual + alive_external

    if not final_list:
        print("[-] Error: no playable streams found.")
        return

    # Sort channels by category order first, then alphabetically by name within each category
    def channel_sort_key(channel):
        group_idx = CATEGORY_INDEX_MAP.get(channel["group"], len(CATEGORY_ORDER))
        channel_name = channel["name"].strip().lower()
        return (group_idx, channel_name)

    final_list.sort(key=channel_sort_key)

    generate_custom_epg(final_list)

    content = [f'#EXTM3U url-tvg="{CUSTOM_EPG_URL}" x-tvg-url="{CUSTOM_EPG_URL}"']
    for ch in final_list:
        tvg_id = sanitize_m3u_attr(ch.get("tvg_id") or ch["name"])
        tvg_name = sanitize_m3u_attr(ch["name"])
        logo = sanitize_m3u_attr(ch.get("logo", ""))
        group = sanitize_m3u_attr(ch["group"])
        name = ch["name"].replace("\r", " ").replace("\n", " ").strip()
        url = ch["url"]
        audio_track = sanitize_m3u_attr(ch.get("audio_track", ""))
        audio_track_str = f' audio-track="{audio_track}"' if audio_track else ""
        catchup_str = format_catchup_attrs(ch.get("catchup_attrs", {}))

        if logo:
            extinf = f'#EXTINF:-1 tvg-id="{tvg_id}" tvg-name="{tvg_name}" tvg-logo="{logo}" group-title="{group}"{audio_track_str}{catchup_str},{name}'
        else:
            extinf = f'#EXTINF:-1 tvg-id="{tvg_id}" tvg-name="{tvg_name}" group-title="{group}"{audio_track_str}{catchup_str},{name}'

        entry_lines = [extinf]
        for opt in format_channel_headers(
            ch.get("vlc_opts", []), ch.get("http_opts", [])
        ):
            entry_lines.append(opt)
        entry_lines.append(url)

        content.append("\n".join(entry_lines))

    tmp_output = f"{OUTPUT_FILE}.tmp"
    with open(tmp_output, "w", encoding="utf-8") as out:
        out.write("\n\n".join(content) + "\n")
    os.replace(tmp_output, OUTPUT_FILE)

    print(f"\n[+] Generation completed successfully!")
    print(f"    - Playlist URL : https://{REPO_OWNER}.github.io/{REPO_NAME}/{OUTPUT_FILE}")
    print(f"    - Custom EPG   : {CUSTOM_EPG_URL}")
    print(f"    - Channels count: {len(final_list)}")


if __name__ == "__main__":
    main()
