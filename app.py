import streamlit as st
import pandas as pd
import sqlite3
import os
import re
import struct
import zlib
import tempfile
import math
import shutil

ICON_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "icon.png")
HAS_ICON = os.path.exists(ICON_PATH)

st.set_page_config(
    page_title="ORD Drainage & Conduit Compliance Audit Hub",
    page_icon=ICON_PATH if HAS_ICON else None,
    layout="wide",
    initial_sidebar_state="expanded"
)

# ----------------------------------------------------------------------------
# OLE COMPOUND FILE & GZIP CONTAINER EXTRACTOR
# ----------------------------------------------------------------------------
MAX_REGULAR = 0xFFFFFFFA
LONG_MAX = 0x7FFFFFFFFFFFFFFF

def read_chain(data, fat, start, ss, max_bytes):
    ms = bytearray()
    s = start
    guard = 0
    while s < MAX_REGULAR and s < len(fat) and guard <= len(fat):
        off = (s + 1) * ss
        if off + ss > len(data): break
        remaining = max_bytes - len(ms)
        if remaining <= 0: break
        take = min(ss, int(remaining))
        ms.extend(data[off:off+take])
        s = fat[s]
        guard += 1
    return bytes(ms)

def gunzip_custom(b):
    flags = b[3]
    pos = 10
    if (flags & 4) != 0:
        xlen = b[pos] | (b[pos + 1] << 8)
        pos += 2 + xlen
    if (flags & 8) != 0:
        while b[pos] != 0: pos += 1
        pos += 1
    if (flags & 16) != 0:
        while b[pos] != 0: pos += 1
        pos += 1
    if (flags & 2) != 0:
        pos += 2
    deobj = zlib.decompressobj(-15)
    return deobj.decompress(b[pos:]) + deobj.flush()

def parse_container(raw):
    list_entries = []
    p = 0
    while p < len(raw):
        nl = raw.find(b"\n", p)
        if nl < 0 or nl - p > 300: break
        line = raw[p:nl].decode("utf-8", errors="ignore")
        m = re.match(r"^(\d+),(\d+),(.+)$", line)
        if not m: break
        size = int(m.group(2))
        if nl + 1 + size > len(raw): break
        list_entries.append({"Name": m.group(3).strip(), "Offset": nl + 1, "Size": size})
        p = nl + 1 + size + 1
    return list_entries

def extract_database_from_uploaded_file(uploaded_file, out_dir):
    data = uploaded_file.read()
    if len(data) < 512 or data[0] != 0xD0 or data[1] != 0xCF or data[2] != 0x11 or data[3] != 0xE0:
        return None, "not_compound"

    ss = 1 << struct.unpack_from("<H", data, 30)[0]
    n_fat = struct.unpack_from("<I", data, 44)[0]
    dir_start = struct.unpack_from("<I", data, 48)[0]
    mini_cutoff = struct.unpack_from("<I", data, 56)[0]
    dif_start = struct.unpack_from("<I", data, 68)[0]
    n_dif = struct.unpack_from("<I", data, 72)[0]

    difat = []
    for i in range(109):
        v = struct.unpack_from("<I", data, 76 + 4 * i)[0]
        if v < MAX_REGULAR: difat.append(v)

    s = dif_start
    k = 0
    while k < n_dif and s < MAX_REGULAR:
        off = (s + 1) * ss
        for j in range(ss // 4 - 1):
            v = struct.unpack_from("<I", data, off + 4 * j)[0]
            if v < MAX_REGULAR: difat.append(v)
        s = struct.unpack_from("<I", data, off + ss - 4)[0]
        k += 1

    fat = []
    for i in range(len(difat)):
        if i >= n_fat: break
        off = (difat[i] + 1) * ss
        if off + ss > len(data): break
        for j in range(ss // 4):
            fat.append(struct.unpack_from("<I", data, off + 4 * j)[0])

    dir_bytes = read_chain(data, fat, dir_start, ss, LONG_MAX)
    has_utility = False
    
    for i in range(0, len(dir_bytes) - 127, 128):
        entry = dir_bytes[i:i+128]
        if entry[66] != 2: continue
        start = struct.unpack_from("<I", entry, 116)[0]
        size = struct.unpack_from("<Q", entry, 120)[0]
        if size < mini_cutoff or size > 0x7FFFFFFF: continue
        stream = read_chain(data, fat, start, ss, size)
        if len(stream) < 20 or stream[0] != 0x1F or stream[1] != 0x8B: continue
        try:
            raw = gunzip_custom(stream)
        except Exception:
            continue
        
        for e in parse_container(raw):
            name_lower = e["Name"].lower()
            if "util" in name_lower:
                has_utility = True
            if ".stsw.sqlite" in name_lower:
                db_bytes = raw[e["Offset"]:e["Offset"] + e["Size"]]
                out_path = os.path.join(out_dir, "extracted_stsw.sqlite")
                with open(out_path, "wb") as out_f:
                    out_f.write(db_bytes)
                return out_path, "success"

    if has_utility:
        return None, "utility_only"
    return None, "no_model"

# ----------------------------------------------------------------------------
# HELPER FUNCTIONS FOR AUDIT
# ----------------------------------------------------------------------------
def norm(label):
    s = str(label).strip().upper() if label is not None else ""
    return "" if s in ("(N/A)", "N/A", "NONE", "NULL") else s

def worse(a, b):
    order = {"N/A": 0, "No Absolute Rotation": 1, "Allowed": 2, "Not Allowed": 3}
    return a if order.get(a, 0) >= order.get(b, 0) else b

def to_inches(v):
    if v is None or v <= 0: return None
    return v * 12.0 if v < 50 else float(v)

def feature_tokens(feature_def):
    return {t for t in re.split(r"[\\_\-\s]+", (feature_def or "").upper()) if t}

def build_structure(feature_def, gtype, dia, length, width):
    CIRCULAR_TOKENS = {"PRM", "ROUND", "CIRCULAR", "CMH"}
    D, L, W = to_inches(dia), to_inches(length), to_inches(width)
    force_circ = bool(feature_tokens(feature_def) & CIRCULAR_TOKENS)
    g = str(gtype).strip().lower() if gtype is not None else ""
    is_circ_type = g in ("0", "circular", "circle", "round")
    if (force_circ or is_circ_type) and D:
        return {"shape": "circular", "length": D, "width": D, "diameter": D}
    if L and W:
        return {"shape": "box", "length": L, "width": W, "diameter": None}
    if D:
        return {"shape": "circular", "length": D, "width": D, "diameter": D}
    return None

def fitting_reason(feature_def, is_junction_chamber):
    FITTING_TOKENS = ("bend", "wye", "tee", "transition", "tap", "reducer", "outfall", "headwall", "endwall", "cross section", "_xs", "xs_")
    fd = (feature_def or "").lower()
    for t in FITTING_TOKENS:
        if t in fd: return f"Fitting/other ({t.strip('_ ')})"
    if is_junction_chamber: return "Fitting/other (junction chamber - no dimensions)"
    return "Not a dimensioned structure"

# ----------------------------------------------------------------------------
# MAIN PROCESSING ENGINE
# ----------------------------------------------------------------------------
@st.cache_data(show_spinner="Running audit...", max_entries=20)
def run_audit(db_path, orientation_map, params):
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()

    cursor.execute("SELECT ElementID, Label FROM HMIModelingElement")
    labels = {r[0]: r[1].strip() for r in cursor.fetchall() if r[1]}

    conduit_feature_defs = {}
    try:
        cursor.execute("SELECT DomainElementID, FeatureDefinition FROM BaseLink")
        for dom_id, fdef in cursor.fetchall():
            if dom_id is not None: conduit_feature_defs[dom_id] = fdef or ""
    except Exception:
        pass

    cursor.execute("SELECT DomainElementID, AlternativeID, ConduitRise, ConduitDiameter, ConduitThickness FROM Conduit_Physical_Data")
    conduits_phys, conduit_alt_map, label_to_cid = {}, {}, {}
    for dom_id, alt_id, rise, diameter, thickness in cursor.fetchall():
        pipe_label = labels.get(dom_id, f"Pipe-{dom_id}").strip()
        fdef = conduit_feature_defs.get(dom_id, "")
        is_ditch = "DITCH" in fdef.upper() or "DITCH" in pipe_label.upper()
        eff_rise = rise if (rise is not None and rise > 0) else (diameter if (diameter is not None and diameter > 0) else 2.0)
        dia_ft = diameter if (diameter is not None and diameter > 0) else eff_rise
        conduits_phys[dom_id] = {
            "ConduitLabel": pipe_label,
            "FeatureDef": fdef,
            "IsDitch": is_ditch,
            "diameter_in": dia_ft * 12.0 if dia_ft < 20 else dia_ft,
            "rise_ft": eff_rise if eff_rise < 20 else eff_rise / 12.0,
            "thickness": thickness if thickness is not None else 3.5,
        }
        conduit_alt_map[dom_id] = alt_id
        label_to_cid[norm(pipe_label)] = dom_id

    ext_data = {}
    try:
        cursor.execute("SELECT DomainElementID, ConstructionLength, ConstructionSlope FROM BaseLink_HMIUserDefinedExtensions_Data")
        for dom_id, length, slope in cursor.fetchall():
            ext_data[dom_id] = {"Length": length or 0.0, "Slope": slope or 0.0}
    except Exception:
        pass

    cursor.execute("PRAGMA table_info(BaseNode_Physical_Data)")
    node_columns = [c[1] for c in cursor.fetchall()]
    max_idx = 1
    while f"Conduit{max_idx}Label" in node_columns: max_idx += 1
    max_idx -= 1

    sel = ["DomainElementID", "Physical_GroundElevation", "OutgoingLabel", "OutgoingInvert"]
    for i in range(1, max_idx + 1): sel += [f"Conduit{i}Label", f"Conduit{i}Invert"]
    cursor.execute(f"SELECT {', '.join(sel)} FROM BaseNode_Physical_Data")

    node_by_outgoing_label, conduit_node_lookup, node_ground_elevations = {}, {}, {}
    for nrow in cursor.fetchall():
        node_id, ground, out_inv = nrow[0], nrow[1] if nrow[1] is not None else 0.0, nrow[3] if nrow[3] is not None else 0.0
        node_ground_elevations[node_id] = ground
        if norm(nrow[2]):
            node_by_outgoing_label[norm(nrow[2])] = {"GroundElevation": ground, "OutgoingInvert": out_inv}
        for i in range(1, max_idx + 1):
            key = norm(nrow[4 + (i - 1) * 2])
            inv = nrow[5 + (i - 1) * 2]
            if key and key not in conduit_node_lookup:
                conduit_node_lookup[key] = {"GroundElevation": ground, "Invert": inv if inv is not None else 0.0}

    # Extract node rotation from node tables (ignoring physical tables to avoid conduit angle columns)
    cursor.execute("SELECT name FROM sqlite_master WHERE type='table' AND name LIKE '%Node%'")
    node_tables = [r[0] for r in cursor.fetchall()]
    node_rotations = {}

    for tbl in node_tables:
        if "physical" in tbl.lower():
            continue
        try:
            cursor.execute(f"PRAGMA table_info({tbl})")
            cols = [c[1].lower() for c in cursor.fetchall()]
            valid_cols = [c for c in cols if not any(kw in c for kw in ("conduit", "pipe", "link", "outgoing", "incoming", "diversion", "drainage"))]
            
            rot_col = next((c for c in valid_cols if "rotation" in c or c in ("angle", "node_rotation", "orientation", "azimuth")), None)
            
            if rot_col:
                cursor.execute(f"SELECT DomainElementID, {rot_col} FROM {tbl}")
                for r in cursor.fetchall():
                    if r[0] is not None and r[1] is not None:
                        val = float(r[1])
                        if abs(val) <= 6.3:
                            val = math.degrees(val)
                        node_rotations[r[0]] = val
        except Exception:
            pass

    struct_raw = {}
    try:
        cursor.execute("SELECT DomainElementID, GravityStructureType, CircularStructureType_Diameter, BoxStructureType_Length, BoxStructureType_Width FROM GravitySurfaceStructure_Physical_Data")
        for row in cursor.fetchall():
            struct_raw.setdefault(row[0], (row[1], row[2], row[3], row[4]))
    except Exception:
        pass

    junction_chambers = set()
    try:
        cursor.execute("SELECT DomainElementID FROM JunctionChamber")
        junction_chambers = {r[0] for r in cursor.fetchall()}
    except Exception:
        pass

    slot_cols = []
    for i in range(1, 6): slot_cols += [f"p.Conduit{i}DrainageID", f"p.Conduit{i}Label", f"p.Conduit{i}Size", f"p.Conduit{i}Angle", f"p.Conduit{i}Invert"]
    for nm in ("Outgoing", "Diversion"): slot_cols += [f"p.{nm}DrainageID", f"p.{nm}Label", f"p.{nm}Size", f"p.{nm}Angle", f"p.{nm}Invert"]
    cursor.execute(f"""SELECT p.DomainElementID, n.FeatureDefinition, p.OutgoingInvert, {', '.join(slot_cols)}
                       FROM BaseNode_Physical_Data p LEFT JOIN BaseNode n ON p.DomainElementID = n.DomainElementID""")
    node_rows = cursor.fetchall()
    conn.close()

    slot_names = ["Conduit 1", "Conduit 2", "Conduit 3", "Conduit 4", "Conduit 5", "Outgoing", "Diversion"]
    audit_results, structure_depth_audit_results = [], []
    conduit_audit_map = {cid: {"ConduitLabel": c["ConduitLabel"], "StartNode": "N/A", "StartStatus": "N/A", "EndNode": "N/A", "EndStatus": "N/A"} for cid, c in conduits_phys.items()}

    seen = set()
    discovered_feature_defs = set()

    for row in node_rows:
        node_id, feature_def = row[0], row[1] or ""
        if feature_def: discovered_feature_defs.add(feature_def)
        node_label = labels.get(node_id, f"Node-{node_id}")
        ground_el = node_ground_elevations.get(node_id, 0.0)

        struct = build_structure(feature_def, *struct_raw[node_id]) if node_id in struct_raw else None
        node_kind = f"Structure ({struct['shape']})" if struct else fitting_reason(feature_def, node_id in junction_chambers)
        orientation_mode = orientation_map.get(feature_def, "long_side")

        for k, slot_name in enumerate(slot_names):
            base_idx = 3 + (k * 5)
            drainage_id, cached_label, size, angle, pipe_invert_at_node = row[base_idx], row[base_idx+1], row[base_idx+2], row[base_idx+3], row[base_idx+4]
            if not (drainage_id and drainage_id > 0) or not norm(cached_label or labels.get(drainage_id)): continue
            
            pair_key = (node_id, drainage_id, slot_name)
            if pair_key in seen: continue
            seen.add(pair_key)

            pipe_label = (cached_label or labels.get(drainage_id, f"Pipe-{drainage_id}")).strip()
            phys_id = label_to_cid.get(norm(pipe_label))
            if phys_id is None: continue

            c = conduits_phys[phys_id]
            if c["IsDitch"]: continue

            internal = c["diameter_in"] if c["diameter_in"] > 0 else ((size * 12.0) if size else 0.0)
            raw_t = c["thickness"]
            wall_in = raw_t * 12.0 if raw_t <= 1.0 else raw_t
            required = internal + 2.0 * wall_in + params["CLEARANCE_IN"]

            note_str = ""
            if struct is None:
                status, face_side, avail = "N/A", "-", None
            elif struct["shape"] == "circular":
                status = "Allowed" if required <= struct["diameter"] + params["TOLERANCE_IN"] else "Not Allowed"
                face_side, avail = "Circular wall (diameter)", struct["diameter"]
            else:
                node_rot_deg = float(node_rotations.get(node_id, 0.0))
                
                if node_rot_deg == 0.0:
                    status = "No Absolute Rotation"
                    face_side, avail = "Box Structure (Relative/Zero Rotation)", None
                    note_str = "Rotation is 0.0° (relative or unset absolute in v10.10)"
                else:
                    pipe_angle_deg = math.degrees(angle) if angle is not None else 0.0
                    rot_status_str = f"{node_rot_deg:.1f}°"
                    rel_deg = (pipe_angle_deg - node_rot_deg) % 360

                    dist_to_cardinal = min(abs(rel_deg - 0), abs(rel_deg - 90), abs(rel_deg - 180), abs(rel_deg - 270), abs(rel_deg - 360))
                    if dist_to_cardinal > params["MAX_ANGLE_DEVIATION_DEG"]:
                        note_str = f"Angle deviation > 7° (skewed {dist_to_cardinal:.1f}°)"

                    is_parallel = (0 <= rel_deg < 45) or (135 <= rel_deg < 225) or (315 <= rel_deg < 360)

                    if orientation_mode == "short_side":
                        if is_parallel:
                            face_side, avail = f"Width Side (Short Side - Rot: {rot_status_str})", struct["width"]
                        else:
                            face_side, avail = f"Length Side (Short Side - Rot: {rot_status_str})", struct["length"]
                    else:
                        if is_parallel:
                            face_side, avail = f"Length Side (Long Side - Rot: {rot_status_str})", struct["length"]
                        else:
                            face_side, avail = f"Width Side (Long Side - Rot: {rot_status_str})", struct["width"]
                    status = "Allowed" if required <= avail + params["TOLERANCE_IN"] else "Not Allowed"            

            entry = conduit_audit_map[phys_id]
            if slot_name in ("Outgoing", "Diversion"):
                if entry["StartNode"] == "N/A": entry["StartNode"] = node_label
                entry["StartStatus"] = worse(entry["StartStatus"], status)
            else:
                if entry["EndNode"] == "N/A": entry["EndNode"] = node_label
                entry["EndStatus"] = worse(entry["EndStatus"], status)

            audit_results.append({
                "NodeLabel": node_label, "NodeType": node_kind, "FeatureDef": feature_def if feature_def else "Default",
                "ConduitLabel": c["ConduitLabel"], "ConnectionSide": slot_name, "FaceSide": face_side,
                "InternalDiameter": internal, "RequiredDim": required, "AvailableFaceLength": avail,
                "Status": status, "Note": note_str
            })

            if struct is not None and pipe_invert_at_node is not None:
                top_of_pipe = pipe_invert_at_node + c["rise_ft"] + (raw_t if raw_t <= 1.0 else raw_t / 12.0)
                v_clearance = ground_el - top_of_pipe
                structure_depth_audit_results.append({
                    "NodeLabel": node_label, "NodeType": node_kind, "GroundElevation": ground_el,
                    "ConduitLabel": c["ConduitLabel"], "ConnectionSide": slot_name, "PipeInvert": pipe_invert_at_node,
                    "TopofPipe": top_of_pipe, "VerticalClearance": v_clearance,
                    "Flag": "Check" if v_clearance < params["MIN_VERTICAL_CLEARANCE"] else "Adequate"
                })

    final_rows = []
    for cid, info in conduit_audit_map.items():
        c = conduits_phys[cid]
        lbl = c["ConduitLabel"]
        ext = ext_data.get(cid, {"Length": 0.0, "Slope": 0.0})
        slope = ext["Slope"]
        rise_ft, raw_t = c["rise_ft"], c["thickness"]
        thick_ft = raw_t if raw_t <= 1.0 else raw_t / 12.0

        s = node_by_outgoing_label.get(norm(lbl), {"GroundElevation": 0.0, "OutgoingInvert": 0.0})
        s_inv, s_cov = s["OutgoingInvert"], (s["GroundElevation"] - (s["OutgoingInvert"] + rise_ft + thick_ft)) if (s["GroundElevation"] > 0 and s["OutgoingInvert"] > 0) else 0.0
        e = conduit_node_lookup.get(norm(lbl), {"GroundElevation": 0.0, "Invert": 0.0})
        e_inv, e_cov = e["Invert"], (e["GroundElevation"] - (e["Invert"] + rise_ft + thick_ft)) if (e["GroundElevation"] > 0 and e["Invert"] > 0) else 0.0

        all_zero_or_na = (
            (ext["Length"] == 0.0 or ext["Length"] is None) and
            (slope == 0.0 or slope is None) and
            (s_inv == 0.0 or s_inv is None) and
            (e_inv == 0.0 or e_inv is None) and
            (s_cov == 0.0 or s_cov is None) and
            (e_cov == 0.0 or e_cov is None)
        )
        if all_zero_or_na:
            continue

        if c["IsDitch"]:
            slope_status = "Allowed" if params["MIN_DITCH_SLOPE"] <= slope <= params["MAX_DITCH_SLOPE"] else "Not Allowed"
            s_cov_status, e_cov_status = "N/A (Ditch)", "N/A (Ditch)"
        else:
            slope_status = "Allowed" if params["MIN_PIPE_SLOPE"] <= slope <= params["MAX_PIPE_SLOPE"] else "Not Allowed"
            s_cov_status = "Adequate" if params["MIN_COVER"] <= s_cov <= params["MAX_COVER"] else "Inadequate"
            e_cov_status = "Adequate" if params["MIN_COVER"] <= e_cov <= params["MAX_COVER"] else "Inadequate"

        final_rows.append({
            "ConduitID": cid, "ConduitLabel": lbl, "Type": "Ditch" if c["IsDitch"] else "Pipe",
            "Length (ft)": ext["Length"], "Slope": slope, "StartInvert": s_inv, "StartCover (ft)": s_cov,
            "StopInvert": e_inv, "StopCover (ft)": e_cov, "SlopeStatus": slope_status,
            "StartCoverStatus": s_cov_status, "StopCoverStatus": e_cov_status
        })

    return pd.DataFrame(final_rows), pd.DataFrame(audit_results), pd.DataFrame(structure_depth_audit_results), sorted(list(discovered_feature_defs))

# ----------------------------------------------------------------------------
# STREAMLIT USER INTERFACE
# ----------------------------------------------------------------------------
if HAS_ICON:
    col_logo, col_title = st.columns([1, 11], vertical_alignment="center")
    with col_logo:
        st.image(ICON_PATH, width=80)
    with col_title:
        st.title("ORD Drainage & Conduit Compliance Audit Hub")
    st.sidebar.image(ICON_PATH, width=64)
else:
    st.title("ORD Drainage & Conduit Compliance Audit Hub")
st.markdown("Upload your ORD DGN file to execute automated slope, cover, face-fit, and vertical clearance audits.")

st.sidebar.header("Audit Criteria & Thresholds")
min_p_slope = st.sidebar.number_input("Min Pipe Slope", value=0.005, format="%.4f")
max_p_slope = st.sidebar.number_input("Max Pipe Slope", value=0.120, format="%.4f")
min_d_slope = st.sidebar.number_input("Min Ditch Slope", value=0.002, format="%.4f")
max_d_slope = st.sidebar.number_input("Max Ditch Slope", value=0.050, format="%.4f")
min_cover = st.sidebar.number_input("Min Cover (ft)", value=2.0, format="%.1f")
max_cover = st.sidebar.number_input("Max Cover (ft)", value=15.0, format="%.1f")
min_v_clearance = st.sidebar.number_input("Min Vertical Clearance (ft)", value=1.5, format="%.1f")
max_angle_dev = st.sidebar.number_input("Max Skew Angle Deviation (°)", value=7.0, format="%.1f")

audit_params = {
    "MIN_PIPE_SLOPE": min_p_slope, "MAX_PIPE_SLOPE": max_p_slope,
    "MIN_DITCH_SLOPE": min_d_slope, "MAX_DITCH_SLOPE": max_d_slope,
    "MIN_COVER": min_cover, "MAX_COVER": max_cover,
    "MIN_VERTICAL_CLEARANCE": min_v_clearance, "MAX_ANGLE_DEVIATION_DEG": max_angle_dev,
    "CLEARANCE_IN": 4.0, "TOLERANCE_IN": 0.01
}

uploaded_dgn = st.file_uploader("Upload ORD DGN File", type=["dgn"])

if uploaded_dgn is not None:
    if "processed_file_name" not in st.session_state or st.session_state.processed_file_name != uploaded_dgn.name:
        st.session_state.processed_file_name = uploaded_dgn.name
        # Remove the previous upload's temporary folder so files do not pile up on the server
        old_dir = st.session_state.get("persist_dir")
        if old_dir and os.path.isdir(old_dir):
            shutil.rmtree(old_dir, ignore_errors=True)
        persist_dir = tempfile.mkdtemp(prefix="ord_audit_")
        st.session_state.persist_dir = persist_dir
        db_path, status = extract_database_from_uploaded_file(uploaded_dgn, persist_dir)
        st.session_state.db_path = db_path
        st.session_state.extract_status = status
        
        if status == "success" and db_path:
            dummy_map = {}
            _, _, _, discovered_feats = run_audit(db_path, dummy_map, audit_params)
            st.session_state.discovered_feats = discovered_feats
            st.session_state.orientation_settings = {feat: "long_side" for feat in discovered_feats}

    db_path = st.session_state.get("db_path")
    status = st.session_state.get("extract_status")
    
    if status == "no_model" or db_path is None:
        if status == "utility_only":
            st.error("There is only a utility model.")
        else:
            st.error("This doesn't have an ORD drainage model.")
    else:
        st.success("Stormwater database successfully extracted and loaded.")
        
        discovered_feats = st.session_state.discovered_feats
        df_audit, df_detail, df_clearance, _ = run_audit(db_path, st.session_state.orientation_settings, audit_params)

        tab_ref, tab_slope, tab_cover, tab_detail, tab_clearance = st.tabs([
            "Reference & Inlet Orientations", 
            "Slope Audit", 
            "Cover Audit", 
            "Connection Details", 
            "Vertical Clearance"
        ])

        with tab_ref:
            st.header("Structure Feature Definitions & Orientation Manager")
            st.markdown("Configure whether each structure feature definition operates under **long_side** or **short_side** orientation rules.")
            
            col_img1, col_img2 = st.columns(2)
            with col_img1:
                st.subheader("Long Side Configuration")
                st.info("[ Placeholder Image: Long Side Orientation ]")
            with col_img2:
                st.subheader("Short Side Configuration")
                st.info("[ Placeholder Image: Short Side Orientation ]")

            st.markdown("---")
            st.subheader("Editable Orientation Reference Table")
            
            updated_settings = {}
            for feat in discovered_feats:
                current_val = st.session_state.orientation_settings.get(feat, "long_side")
                choice = st.selectbox(f"Feature: `{feat}`", options=["long_side", "short_side"], index=0 if current_val=="long_side" else 1, key=f"sel_{feat}")
                updated_settings[feat] = choice
            
            if st.button("Save Orientation Settings"):
                st.session_state.orientation_settings = updated_settings
                st.success("Orientation settings saved! Rerun audit with updated configuration.")
                st.rerun()

        with tab_slope:
            st.header("Conduit Slope & Master Audit Summary")
            cover_cols = ['StartCover (ft)', 'StopCover (ft)', 'StartCoverStatus', 'StopCoverStatus']
            df_slope = df_audit.drop(columns=[col for col in cover_cols if col in df_audit.columns], errors='ignore')

            st.subheader("Filter Data")
            f_col1, f_col2, f_col3 = st.columns(3)
            with f_col1:
                search_label = st.text_input("Search Conduit Label", "", key="slope_search", placeholder="Type label to filter...")
            with f_col2:
                type_filter_s = st.selectbox("Filter Type", options=["All", "Pipe", "Ditch"], key="slope_type")
            with f_col3:
                status_filter = st.selectbox("Filter Slope Status", options=["All", "Allowed", "Not Allowed"], key="slope_status")

            filtered_slope = df_slope.copy()
            total_slope = len(filtered_slope)
            if search_label:
                filtered_slope = filtered_slope[filtered_slope['ConduitLabel'].str.contains(search_label, case=False, na=False)]
            if type_filter_s != "All":
                filtered_slope = filtered_slope[filtered_slope['Type'] == type_filter_s]
            if status_filter != "All":
                filtered_slope = filtered_slope[filtered_slope['SlopeStatus'] == status_filter]

            st.caption(f"**{len(filtered_slope)} out of {total_slope}** filtered")

            def highlight_slope_row(row):
                color = 'background-color: #ffcccc' if row.get('SlopeStatus') == 'Not Allowed' else ''
                return [color] * len(row)

            st.dataframe(filtered_slope.style.apply(highlight_slope_row, axis=1), use_container_width=True)

        with tab_cover:
            st.header("Conduit Cover Depth Audit")
            slope_cols = ['Length (ft)', 'Slope', 'StartInvert', 'StopInvert', 'SlopeStatus']
            df_cover = df_audit.drop(columns=[col for col in slope_cols if col in df_audit.columns], errors='ignore')

            st.subheader("Filter Data")
            fc_col1, fc_col2, fc_col3 = st.columns(3)
            with fc_col1:
                search_label_c = st.text_input("Search Conduit Label", "", key="cover_search", placeholder="Type label to filter...")
            with fc_col2:
                type_filter_c = st.selectbox("Filter Type", options=["All", "Pipe", "Ditch"], key="cover_type")
            with fc_col3:
                cover_status_filter = st.selectbox("Filter Cover Status", options=["All", "Adequate", "Inadequate"], key="cover_status")

            filtered_cover = df_cover.copy()
            total_cover = len(filtered_cover)
            if search_label_c:
                filtered_cover = filtered_cover[filtered_cover['ConduitLabel'].str.contains(search_label_c, case=False, na=False)]
            if type_filter_c != "All":
                filtered_cover = filtered_cover[filtered_cover['Type'] == type_filter_c]
            if cover_status_filter != "All":
                filtered_cover = filtered_cover[
                    (filtered_cover['StartCoverStatus'] == cover_status_filter) | 
                    (filtered_cover['StopCoverStatus'] == cover_status_filter)
                ]

            st.caption(f"**{len(filtered_cover)} out of {total_cover}** filtered")

            def highlight_cover_row(row):
                is_inadequate = (row.get('StartCoverStatus') == 'Inadequate') or (row.get('StopCoverStatus') == 'Inadequate')
                color = 'background-color: #ffcccc' if is_inadequate else ''
                return [color] * len(row)

            st.dataframe(filtered_cover.style.apply(highlight_cover_row, axis=1), use_container_width=True)

        with tab_detail:
            st.header("Node-to-Conduit Connection Face-Fit Details")
            st.subheader("Filter Data")
            fd_col1, fd_col2 = st.columns(2)
            with fd_col1:
                search_node = st.text_input("Search Node Label", "", key="detail_search", placeholder="Type node to filter...")
            with fd_col2:
                status_filter_d = st.selectbox("Filter Connection Status", options=["All", "Allowed", "Not Allowed"], key="detail_status")

            filtered_detail = df_detail.copy()
            total_detail = len(filtered_detail)
            if search_node:
                filtered_detail = filtered_detail[filtered_detail['NodeLabel'].str.contains(search_node, case=False, na=False)]
            if status_filter_d != "All":
                filtered_detail = filtered_detail[filtered_detail['Status'] == status_filter_d]

            st.caption(f"**{len(filtered_detail)} out of {total_detail}** filtered")

            def highlight_detail_row(row):
                color = 'background-color: #ffcccc' if row.get('Status') == 'Not Allowed' else ''
                return [color] * len(row)

            st.dataframe(
                filtered_detail.style.apply(highlight_detail_row, axis=1), 
                use_container_width=True,
                column_config={
                    "Note": st.column_config.TextColumn("Note", width="large")
                }
            )

        with tab_clearance:
            st.header("Structure Vertical Clearance Analysis")
            st.subheader("Filter Data")
            fcl_col1, fcl_col2 = st.columns(2)
            with fcl_col1:
                search_node_cl = st.text_input("Search Node Label", "", key="clearance_search", placeholder="Type node to filter...")
            with fcl_col2:
                flag_filter = st.selectbox("Filter Clearance Flag", options=["All", "Check", "Adequate"], key="clearance_flag")

            filtered_clearance = df_clearance.copy()
            total_clearance = len(filtered_clearance)
            if search_node_cl:
                filtered_clearance = filtered_clearance[filtered_clearance['NodeLabel'].str.contains(search_node_cl, case=False, na=False)]
            if flag_filter != "All":
                filtered_clearance = filtered_clearance[filtered_clearance['Flag'] == flag_filter]

            st.caption(f"**{len(filtered_clearance)} out of {total_clearance}** filtered")

            def highlight_clearance_row(row):
                color = 'background-color: #ffcccc' if row.get('Flag') == 'Check' else ''
                return [color] * len(row)

            st.dataframe(filtered_clearance.style.apply(highlight_clearance_row, axis=1), use_container_width=True)