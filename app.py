import re
import time
import math
import hashlib
import random
from dataclasses import dataclass, asdict
from typing import List, Dict, Optional, Callable
from urllib.parse import urljoin, urlparse, urlunparse

import requests
from bs4 import BeautifulSoup
from flask import Flask, render_template_string, abort, redirect, url_for, request

# -----------------------------
# Toggle browser loading for protected sites
# -----------------------------
USE_PLAYWRIGHT_FOR_DOMAIN = True
USE_PLAYWRIGHT_FOR_REA = True  # realestate.com.au

try:
    from playwright.sync_api import sync_playwright  # type: ignore
    PLAYWRIGHT_AVAILABLE = True
except Exception:
    PLAYWRIGHT_AVAILABLE = False

# -----------------------------
# Updated source URLs (as requested)
# -----------------------------
RAYWHITE_BASE = "https://raywhitegladstone.com.au"
RAYWHITE_SEARCH_URL = f"{RAYWHITE_BASE}/properties/residential-for-sale"
RAYWHITE_PARAMS = {
    "category": "",
    "keywords": "",
    "maxFloor": 0,
    "maxLand": 0,
    "minBaths": 0,
    "minBeds": 0,
    "minCars": 0,
    "minFloor": 0,
    "minLand": 1000,
    "price": "",
    "sort": "creationTime desc",
    "suburbPostCode": "",
}

DOMAIN_SEARCH_URL = (
    "https://www.domain.com.au/sale/gladstone-qld-4680/"
    "?ptype=new-land,vacant-land&landsize=1000-any&landsizeunit=m2"
)
DOMAIN_BASE = "https://www.domain.com.au"

REA_SEARCH_URL = (
    "https://www.realestate.com.au/buy/size-1000-in-gladstone+-+greater+region,+qld/list-1"
)
REA_BASE = "https://www.realestate.com.au"

HEADERS = {"User-Agent": "Mozilla/5.0 (compatible; listings-browser/1.5)"}
SESSION = requests.Session()
SESSION.headers.update(HEADERS)

app = Flask(__name__)

# -----------------------------
# Cache
# -----------------------------
CACHE_TTL_SECONDS = 30 * 60  # 30 minutes


@dataclass
class Listing:
    id: str
    source: str  # "raywhite" | "domain" | "rea"
    title: str
    url: str

    image_url: Optional[str] = None

    price_text: Optional[str] = None
    price_num: Optional[float] = None

    beds: Optional[int] = None
    baths: Optional[int] = None
    cars: Optional[int] = None

    land_text: Optional[str] = None
    land_m2: Optional[float] = None

    property_type: Optional[str] = None
    suburb_postcode: Optional[str] = None


_cache = {"ts": 0.0, "listings": [], "by_id": {}}


# -----------------------------
# Utilities
# -----------------------------
def make_id(url: str) -> str:
    return hashlib.sha1(url.encode("utf-8")).hexdigest()[:10]


def first_match(pattern: str, text: str, flags: int = 0) -> Optional[str]:
    m = re.search(pattern, text, flags)
    return m.group(1).strip() if m else None


def normalize_title(s: str) -> str:
    s = (s or "").lower()
    s = re.sub(r"\b(qld|queensland)\b", "", s)
    s = re.sub(r"\b(australia)\b", "", s)
    s = re.sub(r"[^a-z0-9]+", " ", s)
    s = re.sub(r"\s+", " ", s).strip()
    return s


def canonical_url(u: str) -> str:
    p = urlparse(u)
    return urlunparse((p.scheme, p.netloc, p.path, p.params, p.query, ""))


def meta_content(soup: BeautifulSoup, prop: str) -> Optional[str]:
    tag = soup.find("meta", property=prop)
    if tag and tag.get("content"):
        return tag["content"].strip()
    return None


def meta_name(soup: BeautifulSoup, name: str) -> Optional[str]:
    tag = soup.find("meta", attrs={"name": name})
    if tag and tag.get("content"):
        return tag["content"].strip()
    return None


def meta_image(soup: BeautifulSoup) -> Optional[str]:
    return meta_content(soup, "og:image") or meta_name(soup, "twitter:image")


def parse_money_best_effort(text: Optional[str]) -> Optional[float]:
    if not text:
        return None
    m = re.search(r"\$\s*([0-9][0-9,\.]*)", text)
    if not m:
        return None
    raw = m.group(1).replace(",", "").strip()
    try:
        return float(raw)
    except ValueError:
        return None


def parse_land_to_m2_best_effort(text: Optional[str]) -> Optional[float]:
    if not text:
        return None
    t = text.replace(" ", "")

    m = re.search(r"([0-9][0-9,\.]*)m²|([0-9][0-9,\.]*)m2", t, flags=re.I)
    if m:
        num = (m.group(1) or m.group(2)).replace(",", "")
        try:
            return float(num)
        except ValueError:
            return None

    m = re.search(r"([0-9][0-9,\.]*)ha", t, flags=re.I)
    if m:
        num = m.group(1).replace(",", "")
        try:
            return float(num) * 10000.0
        except ValueError:
            return None

    m = re.search(r"([0-9][0-9,\.]*)acres?", t, flags=re.I)
    if m:
        num = m.group(1).replace(",", "")
        try:
            return float(num) * 4046.8564224
        except ValueError:
            return None

    return None


def polite_sleep(a: float = 0.25, b: float = 0.7) -> None:
    time.sleep(random.uniform(a, b))


def fetch_html_requests(url: str, timeout: int = 30) -> str:
    r = SESSION.get(url, timeout=timeout)
    r.raise_for_status()
    return r.text


def fetch_html_chromium(url: str, wait_ms: int = 2500) -> str:
    if not PLAYWRIGHT_AVAILABLE:
        raise RuntimeError("Playwright not installed. Install playwright or disable Chromium fetch.")
    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True)
        context = browser.new_context(
            user_agent=(
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/122.0.0.0 Safari/537.36"
            )
        )
        page = context.new_page()
        page.goto(url, wait_until="domcontentloaded", timeout=60000)
        page.wait_for_timeout(wait_ms)
        html = page.content()
        context.close()
        browser.close()
        return html


# -----------------------------
# Extractors for "quick reference details"
# -----------------------------
def extract_suburb_postcode_from_title(title: Optional[str]) -> Optional[str]:
    if not title:
        return None
    m = re.search(r"([A-Za-z'\-\s]+),?\s*(?:QLD|Queensland)\s*(\d{4})\b", title)
    if m:
        suburb = re.sub(r"\s+", " ", m.group(1)).strip()
        return f"{suburb} {m.group(2)}"
    return None


def extract_property_type(text: str) -> Optional[str]:
    candidates = [
        "Vacant Land", "New Land", "Land", "House", "Unit", "Apartment",
        "Townhouse", "Acreage", "Rural", "Block of Units", "Duplex"
    ]
    low = text.lower()
    for c in candidates:
        if c.lower() in low:
            return c
    return None


def extract_price_text(text: str, fallback_meta: Optional[str] = None) -> Optional[str]:
    m = re.search(
        r"(?im)^(OFFERS OVER|Offers over|AUCTION|Auction|CONTACT AGENT|Contact Agent|FOR SALE|For Sale|"
        r"Expressions of Interest|EXPRESSIONS OF INTEREST|Under\s+Contract|Under\s+offer|Price\s+guide).*$",
        text
    )
    if m:
        return m.group(0).strip()

    m = re.search(r"(?im)^\s*(\$\s*[0-9][0-9,\. ]*(?:m|k)?).*$", text)
    if m:
        line = m.group(0).strip()
        return line[:120]

    if fallback_meta:
        mm = re.search(r"(\$\s*[0-9][0-9,\. ]+)", fallback_meta)
        if mm:
            return mm.group(1).strip()

    return None


# -----------------------------
# Ray White (requests)
# -----------------------------
def raywhite_search_urls() -> List[Dict[str, str]]:
    url = requests.Request("GET", RAYWHITE_SEARCH_URL, params=RAYWHITE_PARAMS).prepare().url
    html = fetch_html_requests(url)
    soup = BeautifulSoup(html, "html.parser")

    found = []
    for a in soup.select("h2 a"):
        href = a.get("href")
        title = a.get_text(" ", strip=True)
        if href and title and "/properties/" in href:
            found.append({"title": title, "url": urljoin(RAYWHITE_BASE, href)})

    seen = set()
    out = []
    for x in found:
        u = canonical_url(x["url"])
        if u in seen:
            continue
        seen.add(u)
        out.append({"title": x["title"], "url": u})
    return out


def raywhite_parse_listing(url: str) -> Dict:
    html = fetch_html_requests(url)
    soup = BeautifulSoup(html, "html.parser")
    text = soup.get_text("\n", strip=True)

    title = soup.find("h1").get_text(" ", strip=True) if soup.find("h1") else None
    meta_desc = meta_content(soup, "og:description") or meta_name(soup, "description")

    price_text = extract_price_text(text, fallback_meta=meta_desc)

    beds = first_match(r"\b(\d+)\s+Beds\b", text)
    baths = first_match(r"\b(\d+)\s+Baths?\b", text)
    cars = first_match(r"\b(\d+)\s+Cars\b", text)

    land_text = first_match(r"\bLand:\s*([^\n]{0,120})", text)

    ptype = None
    m = re.search(r"/(house|land|unit|apartment|townhouse)/", url, flags=re.I)
    if m:
        ptype = m.group(1).title()

    suburb_postcode = extract_suburb_postcode_from_title(title)

    return {
        "title": title,
        "image_url": meta_image(soup),
        "price_text": price_text,
        "beds": int(beds) if beds and beds.isdigit() else None,
        "baths": int(baths) if baths and baths.isdigit() else None,
        "cars": int(cars) if cars and cars.isdigit() else None,
        "land_text": land_text,
        "property_type": ptype or extract_property_type(text) or extract_property_type(meta_desc or ""),
        "suburb_postcode": suburb_postcode,
    }


# -----------------------------
# Domain (Chromium preferred)
# -----------------------------
def domain_fetch_html(url: str) -> str:
    if USE_PLAYWRIGHT_FOR_DOMAIN and PLAYWRIGHT_AVAILABLE:
        return fetch_html_chromium(url, wait_ms=2500)
    return fetch_html_requests(url, timeout=45)


def domain_search_urls() -> List[Dict[str, str]]:
    html = domain_fetch_html(DOMAIN_SEARCH_URL)
    soup = BeautifulSoup(html, "html.parser")

    found = []
    for a in soup.find_all("a", href=True):
        full = urljoin(DOMAIN_BASE, a["href"].strip())
        if not full.startswith(DOMAIN_BASE + "/"):
            continue
        if not re.search(r"-\d{7,}$", full):
            continue
        title = a.get_text(" ", strip=True) or None
        found.append({"title": title, "url": canonical_url(full)})

    seen = set()
    out = []
    for x in found:
        if x["url"] in seen:
            continue
        seen.add(x["url"])
        out.append(x)
    return out


def domain_parse_listing(url: str) -> Dict:
    html = domain_fetch_html(url)
    soup = BeautifulSoup(html, "html.parser")
    text = soup.get_text("\n", strip=True)

    title = soup.find("h1").get_text(" ", strip=True) if soup.find("h1") else None
    meta_desc = meta_content(soup, "og:description") or meta_name(soup, "description") or meta_name(soup, "twitter:description")

    price_text = extract_price_text(text, fallback_meta=meta_desc)

    beds = first_match(r"\b(\d+)\s+Beds\b", text)
    baths = first_match(r"\b(\d+)\s+Baths?\b", text)
    cars = first_match(r"\b(\d+)\s+(?:Parking|Cars)\b", text)

    land_text = None
    m = re.search(r"\b([0-9][0-9,\.]*)\s*(m²|m2|ha|acres?)\b", text, flags=re.I)
    if m:
        land_text = f"{m.group(1)}{m.group(2)}"

    suburb_postcode = extract_suburb_postcode_from_title(title)

    return {
        "title": title,
        "image_url": meta_image(soup),
        "price_text": price_text,
        "beds": int(beds) if beds and beds.isdigit() else None,
        "baths": int(baths) if baths and baths.isdigit() else None,
        "cars": int(cars) if cars and cars.isdigit() else None,
        "land_text": land_text,
        "property_type": extract_property_type(text) or extract_property_type(meta_desc or ""),
        "suburb_postcode": suburb_postcode,
    }


# -----------------------------
# realestate.com.au (Chromium preferred)
# -----------------------------
def rea_fetch_html(url: str) -> str:
    if USE_PLAYWRIGHT_FOR_REA and PLAYWRIGHT_AVAILABLE:
        return fetch_html_chromium(url, wait_ms=3000)
    return fetch_html_requests(url, timeout=45)


def rea_search_urls() -> List[Dict[str, str]]:
    html = rea_fetch_html(REA_SEARCH_URL)
    soup = BeautifulSoup(html, "html.parser")

    found = []
    for a in soup.find_all("a", href=True):
        href = a["href"].strip()
        full = urljoin(REA_BASE, href)
        if not full.startswith(REA_BASE + "/property-"):
            continue
        found.append({"title": a.get_text(" ", strip=True) or None, "url": canonical_url(full)})

    seen = set()
    out = []
    for x in found:
        if x["url"] in seen:
            continue
        seen.add(x["url"])
        out.append(x)
    return out


def rea_parse_listing(url: str) -> Dict:
    html = rea_fetch_html(url)
    soup = BeautifulSoup(html, "html.parser")
    text = soup.get_text("\n", strip=True)

    title = soup.find("h1").get_text(" ", strip=True) if soup.find("h1") else None
    meta_desc = meta_content(soup, "og:description") or meta_name(soup, "description") or meta_name(soup, "twitter:description")

    price_text = extract_price_text(text, fallback_meta=meta_desc)

    beds = first_match(r"\b(\d+)\s*bed", text, flags=re.I)
    baths = first_match(r"\b(\d+)\s*bath", text, flags=re.I)
    cars = first_match(r"\b(\d+)\s*(?:car|parking)", text, flags=re.I)

    land_text = None
    m = re.search(r"\b([0-9][0-9,\.]*)\s*(m²|m2|ha|acres?)\b", text, flags=re.I)
    if m:
        land_text = f"{m.group(1)}{m.group(2)}"

    suburb_postcode = extract_suburb_postcode_from_title(title)

    ptype = None
    m = re.search(r"/property-([a-z\-]+)-", url, flags=re.I)
    if m:
        ptype = m.group(1).replace("-", " ").title()

    return {
        "title": title,
        "image_url": meta_image(soup),
        "price_text": price_text,
        "beds": int(beds) if beds and beds.isdigit() else None,
        "baths": int(baths) if baths and baths.isdigit() else None,
        "cars": int(cars) if cars and cars.isdigit() else None,
        "land_text": land_text,
        "property_type": ptype or extract_property_type(text) or extract_property_type(meta_desc or ""),
        "suburb_postcode": suburb_postcode,
    }


# -----------------------------
# Combine + Dedupe + Sort
# -----------------------------
def refresh_cache(force: bool = False) -> None:
    now = time.time()
    if not force and (now - _cache["ts"] < CACHE_TTL_SECONDS) and _cache["listings"]:
        return

    combined: List[Listing] = []

    sources: List[tuple[str, Callable[[], List[Dict[str, str]]], Callable[[str], Dict]]] = [
        ("raywhite", raywhite_search_urls, raywhite_parse_listing),
        ("domain", domain_search_urls, domain_parse_listing),
        ("rea", rea_search_urls, rea_parse_listing),
    ]

    for source_name, search_fn, parse_fn in sources:
        base_list = search_fn()

        for item in base_list:
            url = canonical_url(item["url"])
            lid = make_id(url)

            details = {}
            try:
                details = parse_fn(url)
            except Exception:
                details = {}

            title = details.get("title") or item.get("title") or url
            price_text = details.get("price_text")
            land_text = details.get("land_text")

            combined.append(
                Listing(
                    id=lid,
                    source=source_name,
                    title=title,
                    url=url,
                    image_url=details.get("image_url"),
                    price_text=price_text,
                    price_num=parse_money_best_effort(price_text),
                    beds=details.get("beds"),
                    baths=details.get("baths"),
                    cars=details.get("cars"),
                    land_text=land_text,
                    land_m2=parse_land_to_m2_best_effort(land_text),
                    property_type=details.get("property_type"),
                    suburb_postcode=details.get("suburb_postcode"),
                )
            )
            polite_sleep()

    seen = set()
    deduped: List[Listing] = []
    for l in combined:
        key = normalize_title(l.title) or l.url
        if key in seen:
            continue
        seen.add(key)
        deduped.append(l)

    _cache["ts"] = now
    _cache["listings"] = deduped
    _cache["by_id"] = {l.id: l for l in deduped}


def sort_listings(listings: List[Listing], sort_key: str) -> List[Listing]:
    if sort_key == "newest":
        return listings

    def safe_num(x: Optional[float], fallback: float) -> float:
        return x if (x is not None and not math.isnan(x)) else fallback

    if sort_key == "price_asc":
        return sorted(listings, key=lambda l: safe_num(l.price_num, float("inf")))
    if sort_key == "price_desc":
        return sorted(listings, key=lambda l: safe_num(l.price_num, -float("inf")), reverse=True)

    if sort_key == "land_asc":
        return sorted(listings, key=lambda l: safe_num(l.land_m2, float("inf")))
    if sort_key == "land_desc":
        return sorted(listings, key=lambda l: safe_num(l.land_m2, -float("inf")), reverse=True)

    if sort_key == "beds_asc":
        return sorted(listings, key=lambda l: safe_num(l.beds, float("inf")))
    if sort_key == "beds_desc":
        return sorted(listings, key=lambda l: safe_num(l.beds, -float("inf")), reverse=True)

    if sort_key == "baths_asc":
        return sorted(listings, key=lambda l: safe_num(l.baths, float("inf")))
    if sort_key == "baths_desc":
        return sorted(listings, key=lambda l: safe_num(l.baths, -float("inf")), reverse=True)

    return listings


# -----------------------------
# UI Templates
# -----------------------------
INDEX_TMPL = """
<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8"/>
  <meta name="viewport" content="width=device-width, initial-scale=1"/>
  <title>Gladstone Listings</title>
  <style>
    :root { --bg:#0b1020; --card:#121a33; --muted:#98a2b3; --text:#e6e9f2; --accent:#7dd3fc; --line: rgba(255,255,255,.09); }
    body { margin:0; font-family: ui-sans-serif, system-ui, -apple-system, Segoe UI, Roboto, Arial;
           background: radial-gradient(1200px 800px at 20% 0%, #1b2550 0%, var(--bg) 55%);
           color: var(--text); }
    .wrap { max-width: 1200px; margin: 0 auto; padding: 28px 18px 60px; }
    header { display:flex; align-items: end; justify-content: space-between; gap: 14px; flex-wrap: wrap;}
    h1 { margin:0; font-size: 22px; letter-spacing: .2px; }
    .sub { color: var(--muted); font-size: 14px; margin-top: 6px; }
    .bar { display:flex; gap:10px; align-items:center; flex-wrap: wrap; }
    .btn { display:inline-block; padding: 10px 12px; border-radius: 10px;
           background: rgba(125,211,252,.12); color: var(--accent); text-decoration:none;
           border: 1px solid rgba(125,211,252,.22); }
    .btn:hover { background: rgba(125,211,252,.18); }
    .select {
      background: rgba(18,26,51,.86);
      border: 1px solid var(--line);
      color: var(--text);
      border-radius: 10px;
      padding: 10px 12px;
      outline: none;
    }
    .grid { margin-top: 18px; display:grid; grid-template-columns: repeat( auto-fit, minmax(320px, 1fr) ); gap: 14px; }
    .card { overflow:hidden; background: rgba(18,26,51,.86); border: 1px solid var(--line);
            border-radius: 18px; box-shadow: 0 16px 40px rgba(0,0,0,.25); display:flex; flex-direction: column; }
    .thumb { width:100%; aspect-ratio: 16/9; background: rgba(255,255,255,.06); display:flex; align-items:center; justify-content:center; }
    .thumb img { width:100%; height:100%; object-fit: cover; display:block; }
    .thumb .noimg { color: var(--muted); font-size: 13px; }
    .body { padding: 14px 14px 12px; }
    .topline { display:flex; align-items:baseline; justify-content: space-between; gap: 10px; }
    .title { font-weight: 650; font-size: 16px; line-height: 1.25; margin: 0; }
    .title a { color: var(--text); text-decoration:none; }
    .title a:hover { color: var(--accent); }
    .price { font-size: 14px; color: var(--accent); white-space: nowrap; }
    .meta { display:flex; flex-wrap: wrap; gap: 8px; color: var(--muted); font-size: 13px; margin-top: 10px; }
    .pill { padding: 5px 8px; border-radius: 999px; background: rgba(255,255,255,.06); border: 1px solid rgba(255,255,255,.07); }
    .src { margin-left: auto; }
    .loc { margin-top: 10px; color: var(--muted); font-size: 13px; }
    footer { margin-top: 22px; color: var(--muted); font-size: 12px; line-height: 1.35; }
  </style>
</head>
<body>
  <div class="wrap">
    <header>
      <div>
        <h1>Gladstone listings — Ray White + Domain + realestate.com.au (deduped)</h1>
        <div class="sub">Showing {{ listings|length }} unique listings • Cache refreshed: {{ refreshed_human }}</div>
      </div>

      <div class="bar">
        <form method="get" action="{{ url_for('index') }}">
          <select class="select" name="sort" onchange="this.form.submit()">
            <option value="newest"   {% if sort=='newest' %}selected{% endif %}>Sort: Newest (default)</option>
            <option value="price_asc"  {% if sort=='price_asc' %}selected{% endif %}>Price: Low → High</option>
            <option value="price_desc" {% if sort=='price_desc' %}selected{% endif %}>Price: High → Low</option>
            <option value="land_desc"  {% if sort=='land_desc' %}selected{% endif %}>Land: Large → Small</option>
            <option value="land_asc"   {% if sort=='land_asc' %}selected{% endif %}>Land: Small → Large</option>
            <option value="beds_desc"  {% if sort=='beds_desc' %}selected{% endif %}>Beds: High → Low</option>
            <option value="beds_asc"   {% if sort=='beds_asc' %}selected{% endif %}>Beds: Low → High</option>
            <option value="baths_desc" {% if sort=='baths_desc' %}selected{% endif %}>Baths: High → Low</option>
            <option value="baths_asc"  {% if sort=='baths_asc' %}selected{% endif %}>Baths: Low → High</option>
          </select>
        </form>

        <a class="btn" href="{{ url_for('refresh') }}">Refresh now</a>
        <a class="btn" href="{{ raywhite_source_url }}" target="_blank" rel="noreferrer">Ray White</a>
        <a class="btn" href="{{ domain_source_url }}" target="_blank" rel="noreferrer">Domain</a>
        <a class="btn" href="{{ rea_source_url }}" target="_blank" rel="noreferrer">REA</a>
      </div>
    </header>

    <div class="grid">
      {% for l in listings %}
      <div class="card">
        <div class="thumb">
          {% if l.image_url %}
            <img src="{{ l.image_url }}" alt="Listing image">
          {% else %}
            <div class="noimg">No image found</div>
          {% endif %}
        </div>

        <div class="body">
          <div class="topline">
            <div class="title">
              <a href="{{ url_for('property_detail', listing_id=l.id, sort=sort) }}">{{ l.title }}</a>
            </div>
            {% if l.price_text %}
              <div class="price">{{ l.price_text }}</div>
            {% endif %}
          </div>

          {% if l.suburb_postcode %}
            <div class="loc">📍 {{ l.suburb_postcode }}</div>
          {% endif %}

          <div class="meta">
            {% if l.property_type %}<span class="pill">🏷 {{ l.property_type }}</span>{% endif %}
            {% if l.beds is not none %}<span class="pill">🛏 {{ l.beds }}</span>{% endif %}
            {% if l.baths is not none %}<span class="pill">🛁 {{ l.baths }}</span>{% endif %}
            {% if l.cars is not none %}<span class="pill">🚗 {{ l.cars }}</span>{% endif %}
            {% if l.land_m2 is not none %}<span class="pill">🌿 {{ "{:,.0f}".format(l.land_m2) }} m²</span>{% endif %}
            {% if l.land_text and l.land_m2 is none %}<span class="pill">🌿 {{ l.land_text }}</span>{% endif %}
            <span class="pill src">
              Source:
              {% if l.source=="raywhite" %}Ray White{% elif l.source=="domain" %}Domain{% else %}REA{% endif %}
            </span>
          </div>
        </div>
      </div>
      {% endfor %}
    </div>

    <footer>
      Cards show price when available plus quick reference chips (type/beds/baths/cars/land/location).
      If REA/Domain are slow, increase CACHE_TTL_SECONDS or cap their detail fetches in refresh_cache().
    </footer>
  </div>
</body>
</html>
"""

DETAIL_TMPL = """
<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8"/>
  <meta name="viewport" content="width=device-width, initial-scale=1"/>
  <title>{{ l.title }}</title>
  <style>
    :root { --bg:#0b1020; --card:#121a33; --muted:#98a2b3; --text:#e6e9f2; --accent:#7dd3fc; --line: rgba(255,255,255,.09); }
    body { margin:0; font-family: ui-sans-serif, system-ui, -apple-system, Segoe UI, Roboto, Arial;
           background: radial-gradient(1200px 800px at 20% 0%, #1b2550 0%, var(--bg) 55%);
           color: var(--text); }
    .wrap { max-width: 900px; margin: 0 auto; padding: 28px 18px 60px; }
    .card { overflow:hidden; background: rgba(18,26,51,.86); border: 1px solid var(--line);
            border-radius: 18px; box-shadow: 0 16px 40px rgba(0,0,0,.25); }
    .thumb { width:100%; aspect-ratio: 16/9; background: rgba(255,255,255,.06); }
    .thumb img { width:100%; height:100%; object-fit: cover; display:block; }
    .body { padding: 18px; }
    h1 { margin:0 0 10px; font-size: 22px; }
    .meta { display:flex; flex-wrap: wrap; gap: 8px; color: var(--muted); font-size: 13px; margin-bottom: 14px;}
    .pill { padding: 6px 9px; border-radius: 999px; background: rgba(255,255,255,.06); border: 1px solid rgba(255,255,255,.07); }
    .price { font-size: 16px; color: var(--accent); margin: 6px 0 14px; }
    .bar { display:flex; gap: 10px; flex-wrap: wrap; margin-top: 16px; }
    .btn { display:inline-block; padding: 10px 12px; border-radius: 10px;
           background: rgba(125,211,252,.12); color: var(--accent); text-decoration:none;
           border: 1px solid rgba(125,211,252,.22); }
    .btn:hover { background: rgba(125,211,252,.18); }
  </style>
</head>
<body>
  <div class="wrap">
    <div class="card">
      {% if l.image_url %}
        <div class="thumb"><img src="{{ l.image_url }}" alt="Listing image"></div>
      {% endif %}

      <div class="body">
        <h1>{{ l.title }}</h1>

        {% if l.price_text %}
          <div class="price">{{ l.price_text }}</div>
        {% endif %}

        <div class="meta">
          {% if l.suburb_postcode %}<span class="pill">📍 {{ l.suburb_postcode }}</span>{% endif %}
          {% if l.property_type %}<span class="pill">🏷 {{ l.property_type }}</span>{% endif %}
          <span class="pill">
            Source:
            {% if l.source=="raywhite" %}Ray White{% elif l.source=="domain" %}Domain{% else %}REA{% endif %}
          </span>
          {% if l.beds is not none %}<span class="pill">🛏 Beds: {{ l.beds }}</span>{% endif %}
          {% if l.baths is not none %}<span class="pill">🛁 Baths: {{ l.baths }}</span>{% endif %}
          {% if l.cars is not none %}<span class="pill">🚗 Cars: {{ l.cars }}</span>{% endif %}
          {% if l.land_m2 is not none %}<span class="pill">🌿 {{ "{:,.0f}".format(l.land_m2) }} m²</span>{% endif %}
          {% if l.land_text and l.land_m2 is none %}<span class="pill">🌿 {{ l.land_text }}</span>{% endif %}
        </div>

        <div class="bar">
          <a class="btn" href="{{ url_for('index', sort=sort) }}">← Back</a>
          <a class="btn" href="{{ l.url }}" target="_blank" rel="noreferrer">Open on site</a>
          <a class="btn" href="{{ url_for('refresh') }}">Refresh cache</a>
        </div>
      </div>
    </div>
  </div>
</body>
</html>
"""


# -----------------------------
# Routes
# -----------------------------
@app.route("/")
def index():
    refresh_cache(force=False)
    sort = request.args.get("sort", "newest")
    listings = sort_listings(_cache["listings"], sort)

    refreshed_human = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(_cache["ts"]))
    raywhite_source_url = requests.Request("GET", RAYWHITE_SEARCH_URL, params=RAYWHITE_PARAMS).prepare().url

    return render_template_string(
        INDEX_TMPL,
        listings=[asdict(x) for x in listings],
        refreshed_human=refreshed_human,
        sort=sort,
        raywhite_source_url=raywhite_source_url,
        domain_source_url=DOMAIN_SEARCH_URL,
        rea_source_url=REA_SEARCH_URL,
    )


@app.route("/refresh")
def refresh():
    refresh_cache(force=True)
    return redirect(url_for("index"))


@app.route("/p/<listing_id>")
def property_detail(listing_id: str):
    refresh_cache(force=False)
    l = _cache["by_id"].get(listing_id)
    if not l:
        abort(404)
    sort = request.args.get("sort", "newest")
    return render_template_string(DETAIL_TMPL, l=asdict(l), sort=sort)


if __name__ == "__main__":
    app.run(debug=True, port=5000)
