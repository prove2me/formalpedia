-- Prove2me | solution 1 for Freiman.late_decision_other_valid
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T09:10:15.820032+00:00
-- url     : https://prove2.me/submissions/cacd2a0d-d551-4d96-ac63-377f6624ea2e


import Definitions.Def_Freiman_lateData
import Mathlib.Data.Finset.Dedup
import Mathlib.Tactic.NormNum

/-!
Private source bridges extending the checked other-tree reflection interface.
The public model is unchanged. Rectangle transitions and complete proof-node
lookups are supplied by source-faithful metadata, not by semantic assumptions.
Source: Freiman lateModel, report §15, printed pp. 140–144.
This assembly proves the exact public structural decision target below.
-/

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option Elab.async false

open Freiman

namespace DiscoveryFreimanOtherReflection

private structure WitnessKey where
  lower : ℕ
  upper : ℕ
  rectangle : ℕ

private structure PathKey where
  right3 : Bool
  incoming : List ℕ
  required : List ℕ
  implications : List (ℕ × Option ℕ)

private structure IndexMetadata where
  boundCount : ℕ
  proofCount : ℕ
  witnessCount : ℕ
  pathCount : ℕ
  complement : ℕ → Option ℕ
  proofNode : ℕ → Option LateProofNode
  witnessKey : ℕ → Option WitnessKey
  pathKey : ℕ → Option PathKey
  rectChild : ℕ → Bool → Bool → Option ℕ

/-- Only literal public source projections and midpoint equalities occur here.
In particular there is no assumed decision/proof validator conclusion. -/
private structure MetadataFaithful (C : LateCatalog) (D : IndexMetadata) : Prop where
  bound_count : D.boundCount = C.bounds.size
  proof_count : D.proofCount = C.proofs.size
  witness_count : D.witnessCount = C.witnesses.size
  path_count : D.pathCount = C.paths.size
  complement : ∀ i j, D.complement i = some j →
    lowerHistoryComplement (lateBound C i) = lateBound C j
  proof_node : ∀ pid node, D.proofNode pid = some node →
    C.proofs[pid - 1]?.getD (.pair 0) = node
  witness_key : ∀ wid w, D.witnessKey wid = some w →
    (lateWitnessRow C wid).lower = w.lower ∧
    (lateWitnessRow C wid).upper = w.upper ∧
    (lateWitnessRow C wid).rectangle = w.rectangle
  path_key : ∀ pid p, D.pathKey pid = some p →
    (latePath C pid).right3 = p.right3 ∧
    (latePath C pid).incoming = p.incoming ∧
    (latePath C pid).required = p.required ∧
    (latePath C pid).implications = p.implications
  rect_child : ∀ rid axis right child, D.rectChild rid axis right = some child →
    lateSubrect (lateRectangle C rid) axis right = lateRectangle C child

private def checkRectPair (D : IndexMetadata) (rid : ℕ) (axis : Bool)
    (left right : ℕ → Bool) : Bool :=
  match D.rectChild rid axis false, D.rectChild rid axis true with
  | some l, some r => left l && right r
  | _, _ => false

private theorem checkRectPair_true (D : IndexMetadata) (rid : ℕ) (axis : Bool)
    (left right : ℕ → Bool) (h : checkRectPair D rid axis left right = true) :
    ∃ l r, D.rectChild rid axis false = some l ∧
      D.rectChild rid axis true = some r ∧ left l = true ∧ right r = true := by
  cases hl : D.rectChild rid axis false with
  | none =>
    have hf : false = true := by simpa only [checkRectPair, hl] using h
    cases hf
  | some l =>
    cases hr : D.rectChild rid axis true with
    | none =>
      have hf : false = true := by simpa only [checkRectPair, hl, hr] using h
      cases hf
    | some r =>
      have hab : left l = true ∧ right r = true :=
        Bool.and_eq_true_iff.mp (by simpa only [checkRectPair, hl, hr] using h)
      exact ⟨l, r, rfl, rfl, hab.1, hab.2⟩

private def checkWitness (D : IndexMetadata) (ids : List ℕ) (rid wid : ℕ) : Bool :=
  match D.witnessKey wid with
  | none => false
  | some w => decide (0 < wid ∧ wid ≤ D.witnessCount ∧
      w.lower ∈ ids ∧ w.upper ∈ ids ∧ w.rectangle = rid)

/-- Fuel is exactly the public validator's fuel. IDs do not decrease in the
source DAG, so recursion by proof ID would not be justified. -/
private def checkProof (D : IndexMetadata) : ℕ → List ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => false
  | fuel + 1, ids, rid, pid =>
    decide (0 < pid ∧ pid ≤ D.proofCount) &&
      match D.proofNode pid with
      | none => false
      | some (.pair wid) => checkWitness D ids rid wid
      | some (.split axis left right) =>
        checkRectPair D rid axis
          (fun child => checkProof D fuel ids child left)
          (fun child => checkProof D fuel ids child right)

private def checkImplication (D : IndexMetadata) (ids : List ℕ)
    (rid : ℕ) (imp : ℕ × Option ℕ) : Bool :=
  match imp.2 with
  | none => decide (imp.1 ∈ ids)
  | some pid =>
    match D.complement imp.1 with
    | none => false
    | some neg => checkProof D 1500 (neg :: ids) rid pid

private def checkPath (D : IndexMetadata) (right3 : Bool)
    (ids : List ℕ) (rid pid : ℕ) : Bool :=
  match D.pathKey pid with
  | none => false
  | some p =>
    decide (0 < pid ∧ pid ≤ D.pathCount ∧ p.right3 = right3 ∧
      p.incoming.toFinset = ids.toFinset ∧
      (p.implications.map Prod.fst).toFinset = p.required.toFinset) &&
        p.implications.all (checkImplication D ids rid)

private def checkDecision (D : IndexMetadata) (right3 : Bool) :
    List ℕ → ℕ → LateDecisionTree → Bool
  | ids, rid, .cut bid left right =>
    decide (0 < bid ∧ bid ≤ D.boundCount) &&
      match D.complement bid with
      | none => false
      | some neg => checkDecision D right3 (bid :: ids) rid left &&
          checkDecision D right3 (neg :: ids) rid right
  | ids, rid, .split axis left right =>
    checkRectPair D rid axis
      (fun child => checkDecision D right3 ids child left)
      (fun child => checkDecision D right3 ids child right)
  | ids, rid, .empty pid => checkProof D 1500 ids rid pid
  | ids, rid, .path pid => checkPath D right3 ids rid pid

private theorem bounds_mem_of_id (C : LateCatalog) {i : ℕ} {ids : List ℕ}
    (hi : i ∈ ids) : lateBound C i ∈ lateBounds C ids := by
  exact List.mem_map.mpr ⟨i, hi, rfl⟩

private theorem bounds_set_eq_of_ids (C : LateCatalog) {xs ys : List ℕ}
    (h : xs.toFinset = ys.toFinset) :
    (lateBounds C xs).toFinset = (lateBounds C ys).toFinset := by
  apply List.toFinset.ext
  intro b
  change b ∈ xs.map (lateBound C) ↔ b ∈ ys.map (lateBound C)
  constructor
  · intro hb
    rcases List.mem_map.mp hb with ⟨i, hi, he⟩
    exact List.mem_map.mpr ⟨i, (List.toFinset.ext_iff.mp h i).mp hi, he⟩
  · intro hb
    rcases List.mem_map.mp hb with ⟨i, hi, he⟩
    exact List.mem_map.mpr ⟨i, (List.toFinset.ext_iff.mp h i).mpr hi, he⟩

private theorem checkWitness_sound (C : LateCatalog) (D : IndexMetadata)
    (hD : MetadataFaithful C D) (ids : List ℕ) (rid wid : ℕ)
    (h : checkWitness D ids rid wid = true) :
    lateIndex wid C.witnesses.size ∧
      (lateWitness C wid).lowerBound ∈ lateBounds C ids ∧
      (lateWitness C wid).upperBound ∈ lateBounds C ids ∧
      (lateWitness C wid).rectangle = lateRectangle C rid := by
  cases hw : D.witnessKey wid with
  | none =>
    have hf : false = true := by simpa only [checkWitness, hw] using h
    cases hf
  | some w =>
    have hv : 0 < wid ∧ wid ≤ D.witnessCount ∧
        w.lower ∈ ids ∧ w.upper ∈ ids ∧ w.rectangle = rid :=
      of_decide_eq_true (by simpa only [checkWitness, hw] using h)
    rcases hv with ⟨hp, hle, hlo, hhi, hrid⟩
    have hrow := hD.witness_key wid w hw
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hD.witness_count]
      exact ⟨hp, hle⟩
    · change lateBound C (lateWitnessRow C wid).lower ∈ lateBounds C ids
      rw [hrow.1]
      exact bounds_mem_of_id C hlo
    · change lateBound C (lateWitnessRow C wid).upper ∈ lateBounds C ids
      rw [hrow.2.1]
      exact bounds_mem_of_id C hhi
    · change lateRectangle C (lateWitnessRow C wid).rectangle = lateRectangle C rid
      rw [hrow.2.2, hrid]

private theorem checkProof_sound (C : LateCatalog) (D : IndexMetadata)
    (hD : MetadataFaithful C D) (fuel : ℕ) (ids : List ℕ) (rid pid : ℕ)
    (h : checkProof D fuel ids rid pid = true) :
    lateProofValid C fuel (lateBounds C ids) (lateRectangle C rid) pid := by
  induction fuel generalizing ids rid pid with
  | zero =>
    have hf : false = true := h
    cases hf
  | succ fuel ih =>
    have hc : (decide (0 < pid ∧ pid ≤ D.proofCount) &&
        match D.proofNode pid with
        | none => false
        | some (.pair wid) => checkWitness D ids rid wid
        | some (.split axis left right) => checkRectPair D rid axis
            (fun child => checkProof D fuel ids child left)
            (fun child => checkProof D fuel ids child right)) = true := h
    have hp : lateIndex pid C.proofs.size := by
      rw [← hD.proof_count]
      change 0 < pid ∧ pid ≤ D.proofCount
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
    have hm := (Bool.and_eq_true_iff.mp hc).2
    change lateIndex pid C.proofs.size ∧ _
    refine ⟨hp, ?_⟩
    cases hn : D.proofNode pid with
    | none =>
      have hf : false = true := by simpa only [hn] using hm
      cases hf
    | some node =>
      rw [hD.proof_node pid node hn]
      cases node with
      | pair wid =>
        exact checkWitness_sound C D hD ids rid wid (by simpa only [hn] using hm)
      | split axis left right =>
        have hb : checkRectPair D rid axis
            (fun child => checkProof D fuel ids child left)
            (fun child => checkProof D fuel ids child right) = true := by
          simpa only [hn] using hm
        rcases checkRectPair_true D rid axis _ _ hb with ⟨l, r, hl, hr, hleft, hright⟩
        constructor
        · rw [hD.rect_child rid axis false l hl]
          exact ih ids l left hleft
        · rw [hD.rect_child rid axis true r hr]
          exact ih ids r right hright

private theorem checkImplication_sound (C : LateCatalog) (D : IndexMetadata)
    (hD : MetadataFaithful C D) (ids : List ℕ) (rid : ℕ)
    (imp : ℕ × Option ℕ) (h : checkImplication D ids rid imp = true) :
    match imp.2 with
    | none => lateBound C imp.1 ∈ lateBounds C ids
    | some pid => lateProofValid C 1500
        (lowerHistoryComplement (lateBound C imp.1) :: lateBounds C ids)
        (lateRectangle C rid) pid := by
  rcases imp with ⟨target, choice⟩
  cases choice with
  | none => exact bounds_mem_of_id C (of_decide_eq_true h)
  | some pid =>
    cases hc : D.complement target with
    | none =>
      have hf : false = true := by simpa only [checkImplication, hc] using h
      cases hf
    | some neg =>
      have hp : checkProof D 1500 (neg :: ids) rid pid = true := by
        simpa only [checkImplication, hc] using h
      change lateProofValid C 1500
        (lowerHistoryComplement (lateBound C target) :: lateBounds C ids)
        (lateRectangle C rid) pid
      rw [hD.complement target neg hc]
      exact checkProof_sound C D hD 1500 (neg :: ids) rid pid hp

private theorem checkPath_sound (C : LateCatalog) (D : IndexMetadata)
    (hD : MetadataFaithful C D) (right3 : Bool) (ids : List ℕ) (rid pid : ℕ)
    (h : checkPath D right3 ids rid pid = true) :
    lateDecisionValid C right3 (lateBounds C ids) (lateRectangle C rid) (.path pid) := by
  cases hpath : D.pathKey pid with
  | none =>
    have hf : false = true := by simpa only [checkPath, hpath] using h
    cases hf
  | some p =>
    have hc : (decide (0 < pid ∧ pid ≤ D.pathCount ∧ p.right3 = right3 ∧
        p.incoming.toFinset = ids.toFinset ∧
        (p.implications.map Prod.fst).toFinset = p.required.toFinset) &&
        p.implications.all (checkImplication D ids rid)) = true := by
      simpa only [checkPath, hpath] using h
    rcases of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1 with
      ⟨hp0, hple, hright, hincoming, hcover⟩
    have hall := (Bool.and_eq_true_iff.mp hc).2
    have hpid : lateIndex pid C.paths.size := by
      rw [← hD.path_count]
      exact ⟨hp0, hple⟩
    rcases hD.path_key pid p hpath with ⟨hsright, hsincoming, hsrequired, hsimplications⟩
    change lateIndex pid C.paths.size ∧ _
    refine ⟨hpid, hsright.trans hright, ?_, ?_⟩
    · rw [hsincoming]
      exact bounds_set_eq_of_ids C hincoming
    · change (List.map Prod.fst (latePath C pid).implications).toFinset =
        (latePath C pid).required.toFinset ∧ _
      refine ⟨?_, ?_⟩
      · rw [hsimplications, hsrequired]
        exact hcover
      · intro imp himp
        rw [hsimplications] at himp
        exact checkImplication_sound C D hD ids rid imp (List.all_eq_true.mp hall imp himp)

private theorem checkDecision_sound (C : LateCatalog) (D : IndexMetadata)
    (hD : MetadataFaithful C D) (right3 : Bool) (ids : List ℕ)
    (rid : ℕ) (tree : LateDecisionTree)
    (h : checkDecision D right3 ids rid tree = true) :
    lateDecisionValid C right3 (lateBounds C ids) (lateRectangle C rid) tree := by
  induction tree generalizing ids rid with
  | cut bid left right ihleft ihright =>
    have hc : (decide (0 < bid ∧ bid ≤ D.boundCount) &&
        match D.complement bid with
        | none => false
        | some neg => checkDecision D right3 (bid :: ids) rid left &&
            checkDecision D right3 (neg :: ids) rid right) = true := h
    have hbid : lateIndex bid C.bounds.size := by
      rw [← hD.bound_count]
      change 0 < bid ∧ bid ≤ D.boundCount
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
    have hm := (Bool.and_eq_true_iff.mp hc).2
    cases hcomp : D.complement bid with
    | none =>
      have hf : false = true := by simpa only [hcomp] using hm
      cases hf
    | some neg =>
      have hb : checkDecision D right3 (bid :: ids) rid left = true ∧
          checkDecision D right3 (neg :: ids) rid right = true :=
        Bool.and_eq_true_iff.mp (by simpa only [hcomp] using hm)
      change lateIndex bid C.bounds.size ∧ _
      refine ⟨hbid, ?_, ?_⟩
      · exact ihleft (bid :: ids) rid hb.1
      · rw [hD.complement bid neg hcomp]
        exact ihright (neg :: ids) rid hb.2
  | split axis left right ihleft ihright =>
    have hb : checkRectPair D rid axis
        (fun child => checkDecision D right3 ids child left)
        (fun child => checkDecision D right3 ids child right) = true := h
    rcases checkRectPair_true D rid axis _ _ hb with ⟨l, r, hl, hr, hleft, hright⟩
    change lateDecisionValid C right3 (lateBounds C ids)
        (lateSubrect (lateRectangle C rid) axis false) left ∧
      lateDecisionValid C right3 (lateBounds C ids)
        (lateSubrect (lateRectangle C rid) axis true) right
    constructor
    · rw [hD.rect_child rid axis false l hl]
      exact ihleft ids l hleft
    · rw [hD.rect_child rid axis true r hr]
      exact ihright ids r hright
  | empty pid => exact checkProof_sound C D hD 1500 ids rid pid h
  | path pid => exact checkPath_sound C D hD right3 ids rid pid h

/-- The final rectangle equality is a concrete source obligation. The checked
conclusion retains the public validator's exact fuel1500 at every leaf. -/
private theorem checkDecision_at_root (C : LateCatalog) (D : IndexMetadata)
    (hD : MetadataFaithful C D) (right3 : Bool) (ids : List ℕ)
    (rid : ℕ) (R : CertRectangle) (tree : LateDecisionTree)
    (hR : lateRectangle C rid = R)
    (h : checkDecision D right3 ids rid tree = true) :
    lateDecisionValid C right3 (lateBounds C ids) R tree := by
  rw [← hR]
  exact checkDecision_sound C D hD right3 ids rid tree h



private theorem bound_list (i : ℕ) : lateBound lateCatalog i =
    lateBoundData.toList[i - 1]?.getD lateZeroBound := by
  change lateBoundData[i - 1]?.getD lateZeroBound = _
  rw [Array.getElem?_toList]

private def complementPairs : List (ℕ × ℕ) :=
  [
    (1, 286),
    (2, 287),
    (3, 288),
    (4, 289),
    (5, 290),
    (6, 291),
    (7, 292),
    (8, 293),
    (9, 294),
    (10, 295),
    (11, 296),
    (12, 297),
    (13, 298),
    (14, 299),
    (19, 303),
    (20, 304),
    (21, 305),
    (22, 306),
    (23, 307),
    (24, 308),
    (25, 309),
    (26, 310),
    (27, 311),
    (28, 312),
    (30, 314),
    (33, 317),
    (34, 318),
    (35, 319),
    (36, 320),
    (37, 321),
    (38, 322),
    (40, 324),
    (41, 325),
    (42, 326),
    (43, 327),
    (44, 328),
    (48, 332),
    (53, 336),
    (59, 172),
    (60, 173),
    (61, 174),
    (62, 175),
    (63, 176),
    (64, 177),
    (65, 178),
    (66, 179),
    (67, 180),
    (69, 182),
    (71, 184),
    (73, 186),
    (75, 188),
    (76, 189),
    (83, 196),
    (85, 198),
    (87, 200),
    (88, 201),
    (91, 204),
    (92, 205),
    (94, 207),
    (95, 208),
    (97, 210),
    (99, 212),
    (102, 215),
    (103, 216),
    (104, 217),
    (105, 218),
    (106, 219),
    (109, 222),
    (110, 223),
    (112, 225),
    (113, 226),
    (114, 227),
    (115, 228),
    (116, 229),
    (117, 230),
    (121, 234),
    (123, 236),
    (126, 239),
    (127, 240),
    (131, 244),
    (133, 246),
    (137, 250),
    (141, 254),
    (143, 256),
    (144, 257),
    (145, 259),
    (149, 263),
    (151, 265),
    (181, 68),
    (183, 70),
    (185, 72),
    (187, 74),
    (190, 77),
    (191, 78),
    (192, 79),
    (193, 80),
    (194, 81),
    (195, 82),
    (197, 84),
    (199, 86),
    (202, 89),
    (203, 90),
    (206, 93),
    (209, 96),
    (211, 98),
    (213, 100),
    (214, 101),
    (220, 107),
    (221, 108),
    (222, 109),
    (224, 111),
    (231, 118),
    (232, 119),
    (233, 120),
    (235, 122),
    (237, 124),
    (238, 125),
    (241, 128),
    (242, 129),
    (243, 130),
    (245, 132),
    (247, 134),
    (248, 135),
    (249, 136),
    (251, 138),
    (252, 139),
    (253, 140),
    (255, 142),
    (257, 144),
    (259, 145),
    (260, 146),
    (261, 147),
    (262, 148),
    (263, 149),
    (264, 150),
    (265, 151),
    (266, 152),
    (267, 153),
    (268, 154),
    (269, 155),
    (270, 156),
    (271, 157),
    (272, 158),
    (273, 159),
    (274, 160),
    (275, 161),
    (276, 162),
    (277, 163),
    (278, 164),
    (279, 165),
    (280, 166),
    (281, 167),
    (282, 168),
    (283, 169),
    (284, 170),
    (285, 171),
    (300, 15),
    (301, 16),
    (302, 18),
    (313, 29),
    (315, 31),
    (316, 32),
    (323, 39),
    (328, 44),
    (329, 45),
    (330, 46),
    (331, 47),
    (333, 49),
    (334, 50),
    (335, 51),
    (337, 54),
    (338, 55),
    (339, 56),
    (340, 57),
    (341, 58)
  ]

private theorem complement_map :
    complementPairs.map (fun p => lowerHistoryComplement
      (lateBoundData.toList[p.1 - 1]?.getD lateZeroBound)) =
    complementPairs.map (fun p =>
      lateBoundData.toList[p.2 - 1]?.getD lateZeroBound) := by rfl

private def lookupComplement (i : ℕ) : Option ℕ := complementPairs.lookup i

private theorem lookupComplement_faithful (i j : ℕ)
    (h : lookupComplement i = some j) :
    lowerHistoryComplement (lateBound lateCatalog i) = lateBound lateCatalog j := by
  have hm : (i, j) ∈ complementPairs := by
    rcases List.lookup_eq_some_iff.mp h with ⟨before, after, he, _⟩
    rw [he]
    simp
  have he := List.map_inj_left.mp complement_map (i, j) hm
  rw [bound_list i, bound_list j]
  exact he

private def proofNodes : List LateProofNode :=
  [
    .pair 1,
    .pair 2,
    .pair 3,
    .pair 4,
    .pair 5,
    .pair 6,
    .pair 7,
    .pair 8,
    .pair 9,
    .pair 10,
    .pair 11,
    .pair 12,
    .pair 13,
    .pair 14,
    .pair 15,
    .pair 16,
    .pair 17,
    .pair 18,
    .pair 19,
    .pair 20,
    .pair 21,
    .pair 22,
    .pair 23,
    .pair 24,
    .pair 25,
    .pair 26,
    .pair 27,
    .pair 28,
    .pair 29,
    .pair 30,
    .pair 31,
    .pair 32,
    .pair 33,
    .pair 34,
    .pair 35,
    .pair 36,
    .pair 37,
    .pair 38,
    .pair 39,
    .pair 40,
    .pair 41,
    .pair 42,
    .pair 43,
    .pair 44,
    .pair 45,
    .pair 46,
    .pair 47,
    .pair 48,
    .pair 49,
    .split true 51 52,
    .pair 50,
    .split true 53 54,
    .pair 51,
    .split true 55 56,
    .pair 52,
    .pair 53,
    .pair 54,
    .pair 55,
    .pair 56,
    .pair 57,
    .pair 58,
    .pair 59,
    .pair 60,
    .pair 61,
    .pair 62,
    .pair 63,
    .pair 64,
    .pair 65,
    .pair 66,
    .pair 67,
    .pair 68,
    .pair 69,
    .pair 70,
    .pair 71,
    .pair 72,
    .pair 73,
    .pair 74,
    .pair 75,
    .pair 76,
    .pair 77,
    .pair 78,
    .pair 79,
    .pair 80,
    .pair 81,
    .pair 82,
    .pair 83,
    .pair 84,
    .pair 85,
    .pair 86,
    .pair 87,
    .pair 88,
    .pair 89,
    .pair 90,
    .pair 91,
    .pair 92,
    .pair 93,
    .pair 94,
    .pair 95,
    .pair 96,
    .pair 97,
    .pair 98,
    .pair 99,
    .pair 100,
    .pair 101,
    .pair 102,
    .pair 103,
    .pair 104,
    .pair 105,
    .pair 106,
    .pair 107,
    .pair 108,
    .pair 109,
    .pair 110,
    .pair 111,
    .pair 112,
    .pair 113,
    .pair 114,
    .pair 115,
    .pair 116,
    .pair 117,
    .pair 118,
    .pair 119,
    .pair 120,
    .pair 121,
    .pair 122,
    .pair 123,
    .pair 124,
    .pair 125,
    .pair 126,
    .pair 127,
    .pair 128,
    .pair 129,
    .pair 130,
    .pair 131,
    .pair 132,
    .pair 133,
    .pair 134,
    .pair 135,
    .pair 136,
    .pair 137,
    .pair 138,
    .pair 139,
    .pair 140,
    .pair 141,
    .pair 142,
    .pair 143,
    .pair 144,
    .pair 145,
    .pair 146,
    .pair 147,
    .pair 148,
    .pair 149,
    .pair 150,
    .pair 151,
    .pair 152,
    .pair 153,
    .pair 154,
    .pair 155,
    .pair 156,
    .pair 157,
    .pair 158,
    .pair 159,
    .pair 160,
    .pair 161,
    .pair 162,
    .pair 163,
    .pair 164,
    .pair 165,
    .pair 166,
    .pair 167,
    .pair 168,
    .pair 169,
    .pair 170,
    .pair 171,
    .pair 172,
    .pair 173,
    .pair 174,
    .pair 175,
    .pair 176,
    .pair 177,
    .pair 178,
    .pair 179,
    .pair 180,
    .pair 181,
    .pair 182,
    .pair 183,
    .pair 184,
    .pair 185,
    .pair 186,
    .pair 187,
    .pair 188,
    .pair 189,
    .pair 190,
    .pair 191,
    .pair 192,
    .pair 193,
    .pair 194,
    .pair 195,
    .pair 196,
    .pair 197,
    .pair 198,
    .pair 199,
    .pair 200,
    .pair 201,
    .pair 202,
    .pair 203,
    .pair 204,
    .pair 205,
    .pair 206,
    .pair 207,
    .pair 208,
    .pair 209,
    .pair 210,
    .pair 211,
    .pair 212,
    .pair 213,
    .pair 214,
    .pair 215,
    .pair 216,
    .pair 217,
    .pair 218,
    .pair 219,
    .pair 220,
    .pair 221,
    .pair 222,
    .pair 223,
    .pair 224,
    .pair 225,
    .pair 226,
    .pair 227,
    .pair 228,
    .pair 229,
    .pair 230,
    .pair 231,
    .pair 232,
    .pair 233,
    .pair 234,
    .pair 235,
    .pair 236,
    .pair 237,
    .pair 238,
    .pair 239,
    .pair 240,
    .pair 241,
    .pair 242,
    .pair 243,
    .pair 244,
    .pair 245,
    .pair 246,
    .pair 247,
    .pair 248,
    .pair 249,
    .pair 250,
    .pair 251,
    .pair 252,
    .pair 253,
    .pair 254,
    .pair 255,
    .pair 256,
    .pair 257,
    .pair 258,
    .pair 259,
    .pair 260,
    .pair 261,
    .pair 262,
    .pair 263,
    .pair 264,
    .pair 265,
    .pair 266,
    .pair 267,
    .pair 268,
    .pair 269,
    .pair 270,
    .pair 271,
    .pair 272,
    .pair 273,
    .pair 274,
    .pair 275,
    .pair 276,
    .pair 277,
    .pair 278,
    .pair 279,
    .pair 280,
    .pair 281,
    .pair 282,
    .pair 283,
    .pair 284,
    .pair 285,
    .pair 286,
    .pair 287,
    .pair 288,
    .pair 289,
    .pair 290,
    .pair 291,
    .pair 292,
    .pair 293,
    .pair 294,
    .pair 295,
    .pair 296,
    .pair 297,
    .pair 298,
    .pair 299,
    .pair 300,
    .pair 301,
    .pair 302,
    .pair 303,
    .pair 304,
    .pair 305,
    .pair 306,
    .pair 307,
    .pair 308,
    .pair 309,
    .pair 310,
    .pair 311,
    .pair 312,
    .pair 313,
    .pair 314,
    .pair 315,
    .pair 316,
    .pair 317,
    .pair 318,
    .pair 319,
    .pair 320,
    .pair 321,
    .pair 322,
    .pair 323,
    .pair 324,
    .pair 325,
    .pair 326,
    .pair 327,
    .pair 328,
    .pair 329,
    .pair 330,
    .pair 331,
    .pair 332,
    .pair 333,
    .pair 334,
    .pair 335,
    .pair 336,
    .pair 337,
    .pair 338,
    .pair 339,
    .pair 340,
    .pair 341,
    .pair 342,
    .pair 343,
    .pair 344,
    .pair 345,
    .pair 346,
    .pair 347,
    .pair 348,
    .pair 349,
    .pair 350,
    .pair 351,
    .pair 352,
    .pair 353,
    .pair 354,
    .pair 355,
    .pair 356,
    .pair 357,
    .pair 358,
    .pair 359,
    .pair 360,
    .pair 361,
    .pair 362,
    .pair 363,
    .pair 364,
    .pair 365,
    .pair 366,
    .pair 367,
    .pair 368,
    .pair 369,
    .pair 370,
    .pair 371,
    .pair 372,
    .pair 373,
    .pair 374,
    .pair 375,
    .pair 376,
    .pair 377,
    .pair 378,
    .pair 379,
    .pair 380,
    .pair 381,
    .pair 382,
    .pair 383,
    .pair 384,
    .pair 385,
    .pair 386,
    .pair 387,
    .pair 388,
    .pair 389,
    .pair 390,
    .pair 391,
    .pair 392,
    .pair 393,
    .pair 394,
    .pair 395,
    .pair 396,
    .pair 397,
    .pair 398,
    .pair 399,
    .pair 400,
    .pair 401,
    .pair 402,
    .pair 403,
    .pair 404,
    .pair 405,
    .pair 406,
    .pair 407,
    .pair 408,
    .pair 409,
    .pair 410,
    .pair 411,
    .pair 412,
    .pair 413,
    .pair 414,
    .pair 415,
    .pair 416,
    .pair 417,
    .pair 418,
    .pair 419,
    .pair 420,
    .pair 421,
    .pair 422,
    .pair 423,
    .pair 424,
    .pair 425,
    .pair 426,
    .pair 427,
    .pair 428,
    .pair 429,
    .pair 430,
    .pair 431,
    .pair 432,
    .pair 433,
    .pair 434,
    .pair 435,
    .pair 436,
    .pair 437,
    .pair 438,
    .pair 439,
    .pair 440,
    .pair 441,
    .pair 442,
    .pair 443,
    .pair 444,
    .pair 445,
    .pair 446,
    .pair 447,
    .pair 448,
    .pair 449,
    .pair 450,
    .pair 451,
    .pair 452,
    .pair 453,
    .pair 454,
    .pair 455,
    .pair 456,
    .pair 457,
    .pair 458,
    .pair 459,
    .pair 460,
    .pair 461,
    .pair 462,
    .pair 463,
    .pair 464,
    .pair 465,
    .pair 466,
    .pair 467,
    .pair 468,
    .pair 469,
    .pair 470,
    .pair 471,
    .pair 472,
    .pair 473,
    .pair 474,
    .pair 475,
    .pair 476,
    .pair 477,
    .pair 478,
    .pair 479,
    .pair 480,
    .pair 481,
    .pair 482,
    .pair 483,
    .pair 484,
    .pair 485,
    .pair 486,
    .pair 487,
    .pair 488,
    .pair 489,
    .pair 490,
    .pair 491,
    .pair 492,
    .pair 493,
    .pair 494,
    .pair 495,
    .pair 496,
    .pair 497,
    .pair 498,
    .pair 499,
    .pair 500,
    .pair 501,
    .pair 502,
    .pair 503,
    .pair 504,
    .pair 505,
    .pair 506,
    .pair 507,
    .pair 508,
    .pair 509,
    .pair 510,
    .pair 511,
    .pair 512,
    .pair 513,
    .pair 514,
    .pair 515,
    .pair 516,
    .pair 517,
    .pair 518,
    .pair 519,
    .pair 520,
    .pair 521,
    .pair 522,
    .pair 523,
    .pair 524,
    .pair 525,
    .pair 526,
    .pair 527,
    .pair 528,
    .pair 529,
    .pair 530,
    .pair 531,
    .pair 532,
    .pair 533,
    .pair 534,
    .pair 535,
    .pair 536,
    .pair 537,
    .pair 538,
    .pair 539,
    .pair 540,
    .pair 541,
    .pair 542,
    .pair 543,
    .pair 544,
    .pair 545,
    .pair 546,
    .pair 547,
    .pair 548,
    .pair 549,
    .pair 550,
    .pair 551,
    .pair 552,
    .pair 553,
    .pair 554,
    .pair 555,
    .pair 556,
    .pair 557,
    .pair 558,
    .pair 559,
    .pair 560,
    .pair 561,
    .pair 562,
    .pair 563,
    .pair 564,
    .pair 565,
    .pair 566,
    .pair 567,
    .pair 568,
    .pair 569,
    .pair 570,
    .pair 571,
    .pair 572,
    .pair 573,
    .pair 574,
    .pair 575,
    .pair 576,
    .pair 577,
    .pair 578,
    .pair 579,
    .pair 580,
    .pair 581,
    .pair 582,
    .pair 583,
    .pair 584,
    .pair 585,
    .pair 586,
    .pair 587,
    .pair 588,
    .pair 589,
    .pair 590,
    .pair 591,
    .pair 592,
    .pair 593,
    .pair 594,
    .pair 595,
    .pair 596,
    .pair 597,
    .pair 598,
    .pair 599,
    .pair 600,
    .pair 601,
    .pair 602,
    .pair 603,
    .pair 604,
    .pair 605,
    .pair 606,
    .pair 607,
    .pair 608,
    .pair 609,
    .pair 610,
    .pair 611,
    .pair 612,
    .pair 613,
    .pair 614,
    .pair 615,
    .pair 616,
    .pair 617,
    .pair 618,
    .pair 619,
    .pair 620,
    .pair 621,
    .pair 622,
    .pair 623,
    .pair 624,
    .pair 625,
    .pair 626,
    .pair 627,
    .pair 628,
    .pair 629,
    .pair 630,
    .pair 631,
    .pair 632,
    .pair 633,
    .pair 634,
    .pair 635,
    .pair 636,
    .pair 637,
    .pair 638,
    .pair 639,
    .pair 640,
    .pair 641,
    .pair 642,
    .pair 643,
    .pair 644,
    .pair 645,
    .pair 646,
    .pair 647,
    .pair 648,
    .pair 649,
    .pair 650,
    .pair 651,
    .pair 652,
    .pair 653,
    .pair 654,
    .pair 655,
    .pair 656,
    .pair 657,
    .pair 658,
    .pair 659,
    .pair 660,
    .pair 661,
    .pair 662,
    .pair 663,
    .pair 664,
    .pair 665,
    .pair 666,
    .pair 667,
    .pair 668,
    .pair 669,
    .pair 670,
    .pair 671,
    .pair 672,
    .pair 673,
    .pair 674,
    .pair 675,
    .pair 676,
    .pair 677,
    .pair 678,
    .pair 679,
    .pair 680,
    .pair 681,
    .pair 682,
    .pair 683,
    .pair 684,
    .pair 685,
    .pair 686,
    .pair 687,
    .pair 688,
    .pair 689,
    .pair 690,
    .pair 691,
    .pair 692,
    .pair 693,
    .pair 694,
    .pair 695,
    .pair 696,
    .pair 697,
    .pair 698,
    .pair 699,
    .pair 700,
    .pair 701,
    .pair 702,
    .pair 703,
    .pair 704,
    .pair 705,
    .pair 706,
    .pair 707,
    .pair 708,
    .pair 709,
    .pair 710,
    .pair 711,
    .pair 712,
    .pair 713,
    .pair 714,
    .pair 715,
    .pair 716,
    .pair 717,
    .pair 718,
    .pair 719,
    .pair 720,
    .pair 721,
    .pair 722,
    .pair 723,
    .pair 724,
    .pair 725,
    .pair 726,
    .pair 727,
    .pair 728,
    .pair 729,
    .pair 730,
    .pair 731,
    .pair 732,
    .pair 733,
    .pair 734,
    .pair 735,
    .pair 736,
    .pair 737,
    .pair 738,
    .pair 739,
    .pair 740,
    .pair 741,
    .pair 742,
    .pair 743,
    .pair 744,
    .pair 745,
    .pair 746,
    .pair 747,
    .pair 748,
    .pair 749,
    .pair 750,
    .pair 751,
    .pair 752,
    .pair 753,
    .pair 754,
    .pair 755,
    .pair 756,
    .pair 757,
    .pair 758,
    .pair 759,
    .pair 760,
    .pair 761,
    .pair 762,
    .pair 763,
    .pair 764,
    .pair 765,
    .pair 766,
    .pair 767,
    .pair 768,
    .pair 769,
    .pair 770,
    .pair 771,
    .pair 772,
    .pair 773,
    .pair 774,
    .pair 775,
    .pair 776,
    .pair 777,
    .pair 778,
    .pair 779,
    .split true 784 785,
    .pair 780,
    .pair 781,
    .split true 787 788,
    .pair 782,
    .split true 789 790,
    .pair 783,
    .pair 784,
    .pair 785,
    .pair 786,
    .pair 787,
    .pair 788,
    .pair 789,
    .pair 790,
    .pair 791,
    .pair 792,
    .pair 793,
    .pair 794,
    .pair 795,
    .pair 796,
    .pair 797,
    .pair 798,
    .pair 799,
    .pair 800,
    .pair 801,
    .pair 802,
    .pair 803,
    .pair 804,
    .pair 805,
    .pair 806,
    .pair 807,
    .split true 815 822,
    .split true 816 821,
    .split true 817 818,
    .pair 808,
    .split true 819 820,
    .pair 809,
    .pair 810,
    .pair 811,
    .pair 812,
    .pair 813,
    .pair 814,
    .pair 815,
    .pair 816,
    .pair 817,
    .pair 818,
    .pair 819,
    .pair 820,
    .pair 821,
    .pair 822,
    .pair 823,
    .pair 824,
    .pair 825,
    .pair 826,
    .pair 827,
    .pair 828,
    .pair 829,
    .pair 830,
    .pair 831,
    .pair 832,
    .pair 833,
    .pair 834,
    .pair 835,
    .pair 836,
    .pair 837,
    .pair 838,
    .pair 839,
    .pair 840,
    .pair 841,
    .pair 842,
    .pair 843,
    .pair 844,
    .pair 845,
    .pair 846,
    .pair 847,
    .pair 848,
    .pair 849,
    .pair 850,
    .pair 851,
    .pair 852,
    .pair 853,
    .pair 854,
    .pair 855,
    .pair 856,
    .pair 857,
    .pair 858,
    .pair 859,
    .pair 860,
    .pair 861,
    .pair 862,
    .pair 863,
    .pair 864,
    .pair 865,
    .pair 866,
    .pair 867,
    .pair 868,
    .pair 869,
    .pair 870,
    .pair 871,
    .pair 872,
    .split true 884 885,
    .pair 873,
    .split false 886 887,
    .pair 874,
    .split true 888 889,
    .pair 875,
    .pair 876,
    .pair 877,
    .pair 878,
    .pair 879,
    .pair 880,
    .pair 881,
    .pair 882,
    .pair 883,
    .pair 884,
    .pair 885,
    .pair 886,
    .pair 887,
    .pair 888,
    .pair 889,
    .pair 890,
    .pair 891,
    .pair 892,
    .pair 893,
    .pair 894,
    .pair 895,
    .pair 896,
    .pair 897,
    .pair 898,
    .pair 899,
    .pair 900,
    .pair 901,
    .pair 902,
    .pair 903,
    .pair 904,
    .pair 905,
    .pair 906,
    .pair 907,
    .pair 908,
    .pair 909,
    .pair 910,
    .pair 911,
    .pair 912,
    .pair 913,
    .pair 914,
    .pair 915,
    .pair 916,
    .pair 917,
    .pair 918,
    .pair 919,
    .pair 920,
    .pair 921,
    .pair 922,
    .pair 923,
    .pair 924,
    .pair 925,
    .pair 926,
    .pair 927,
    .pair 928,
    .pair 929,
    .pair 930,
    .pair 931,
    .pair 932,
    .pair 933,
    .pair 934,
    .pair 935,
    .pair 936,
    .pair 937,
    .pair 938,
    .pair 939,
    .pair 940,
    .pair 941,
    .pair 942,
    .pair 943,
    .pair 944,
    .pair 945,
    .pair 946,
    .pair 947,
    .pair 948,
    .pair 949,
    .pair 950,
    .pair 951,
    .pair 952,
    .pair 953,
    .split true 968 969,
    .pair 954,
    .split true 970 971,
    .pair 955,
    .pair 956,
    .pair 957,
    .pair 958,
    .pair 959,
    .pair 960,
    .pair 961,
    .pair 962,
    .split true 968 979,
    .split true 789 980,
    .split true 981 982,
    .pair 963,
    .pair 964,
    .pair 965,
    .pair 966,
    .pair 967,
    .pair 968,
    .pair 969,
    .split true 989 990,
    .pair 970,
    .pair 971,
    .pair 972,
    .pair 973,
    .pair 974,
    .pair 975,
    .pair 976,
    .pair 977,
    .pair 978,
    .pair 979,
    .pair 980,
    .pair 981,
    .pair 982,
    .pair 983,
    .pair 984,
    .pair 985,
    .pair 986,
    .pair 987,
    .pair 988,
    .split true 1009 1010,
    .pair 989,
    .split true 985 971,
    .pair 990,
    .pair 991,
    .pair 992,
    .pair 993,
    .pair 994,
    .pair 995,
    .pair 996,
    .pair 997,
    .pair 998,
    .pair 999,
    .pair 1000,
    .pair 1001,
    .pair 1002,
    .pair 1003,
    .pair 1004,
    .pair 1005,
    .pair 1006,
    .pair 1007,
    .pair 1008,
    .pair 1009,
    .pair 1010,
    .pair 1011,
    .pair 1012,
    .pair 1013,
    .pair 1014,
    .pair 1015,
    .pair 1016,
    .pair 1017,
    .pair 1018,
    .pair 1019,
    .pair 1020,
    .pair 1021,
    .pair 1022,
    .pair 1023,
    .pair 1024,
    .pair 1025,
    .pair 1026,
    .pair 1027,
    .pair 1028,
    .pair 1029,
    .pair 1030,
    .pair 1031,
    .pair 1032,
    .pair 1033,
    .pair 1034,
    .pair 1035,
    .pair 1036,
    .pair 1037,
    .pair 1038,
    .pair 1039,
    .pair 1040,
    .pair 1041,
    .pair 1042,
    .pair 1043,
    .pair 1044,
    .pair 1045,
    .pair 1046,
    .pair 1047,
    .pair 1048,
    .pair 1049,
    .pair 1050,
    .pair 1051,
    .pair 1052,
    .pair 1053,
    .pair 1054,
    .pair 1055,
    .pair 1056,
    .pair 1057,
    .pair 1058,
    .pair 1059,
    .pair 1060,
    .pair 1061,
    .pair 1062,
    .pair 1063,
    .pair 1064,
    .pair 1065,
    .pair 1066,
    .pair 1067,
    .pair 1068,
    .pair 1069
  ]

private theorem proofNodes_eq : lateProofData.toList.take 1090 = proofNodes := by rfl

private def lookupProof (pid : ℕ) : Option LateProofNode :=
  if 0 < pid ∧ pid ≤ 1090 then proofNodes[pid - 1]? else none

private theorem array_prefix_lookup {α : Type} (xs : Array α) (n : ℕ)
    (ys : List α) (hy : xs.toList.take n = ys) (i : ℕ) (hi : i < n) :
    xs[i]? = ys[i]? := by
  rw [← hy, List.getElem?_take_of_lt hi, Array.getElem?_toList]

private theorem lookupProof_faithful (pid : ℕ) (node : LateProofNode)
    (h : lookupProof pid = some node) :
    lateCatalog.proofs[pid - 1]?.getD (.pair 0) = node := by
  unfold lookupProof at h
  split at h
  next hp =>
    have hi : pid - 1 < 1090 := by omega
    have he := array_prefix_lookup lateProofData 1090 proofNodes proofNodes_eq (pid - 1) hi
    exact congrArg (fun o : Option LateProofNode => o.getD (.pair 0)) (he.trans h)
  next => contradiction


private abbrev WKey := ℕ × ℕ × ℕ

private abbrev PKey := Bool × List ℕ × List ℕ × List (ℕ × Option ℕ)

private def witnessKey (w : LateWitnessRow) : WKey := (w.lower, w.upper, w.rectangle)

private def pathKey (p : LatePath) : PKey :=
  (p.right3, p.incoming, p.required, p.implications)

private def witnessKeys : List WKey :=
  [
    (12, 286, 9),
    (12, 287, 9),
    (12, 298, 9),
    (12, 324, 9),
    (12, 327, 9),
    (12, 328, 9),
    (12, 172, 9),
    (12, 174, 9),
    (12, 177, 9),
    (12, 184, 9),
    (12, 200, 9),
    (12, 204, 9),
    (12, 210, 9),
    (12, 217, 9),
    (12, 218, 9),
    (12, 219, 9),
    (12, 225, 9),
    (12, 229, 9),
    (12, 236, 9),
    (12, 240, 9),
    (12, 244, 9),
    (12, 254, 9),
    (12, 257, 9),
    (12, 265, 9),
    (90, 258, 9),
    (100, 258, 9),
    (111, 258, 9),
    (122, 258, 9),
    (130, 258, 9),
    (147, 258, 9),
    (150, 258, 9),
    (152, 258, 9),
    (154, 258, 9),
    (157, 258, 9),
    (158, 258, 9),
    (160, 258, 9),
    (161, 258, 9),
    (167, 258, 9),
    (169, 258, 9),
    (170, 258, 9),
    (15, 258, 9),
    (29, 258, 9),
    (32, 258, 9),
    (45, 258, 9),
    (49, 258, 9),
    (51, 258, 9),
    (54, 258, 9),
    (56, 258, 9),
    (58, 258, 9),
    (145, 258, 8),
    (145, 258, 18),
    (145, 258, 20),
    (12, 258, 23),
    (149, 286, 9),
    (149, 288, 9),
    (149, 298, 9),
    (149, 311, 9),
    (149, 327, 9),
    (149, 328, 9),
    (149, 172, 9),
    (149, 174, 9),
    (149, 184, 9),
    (149, 200, 9),
    (149, 210, 9),
    (149, 219, 9),
    (149, 240, 9),
    (149, 244, 9),
    (149, 254, 9),
    (149, 257, 9),
    (111, 297, 9),
    (122, 297, 9),
    (130, 297, 9),
    (139, 297, 9),
    (145, 194, 9),
    (150, 297, 9),
    (152, 297, 9),
    (157, 297, 9),
    (158, 297, 9),
    (161, 297, 9),
    (163, 297, 9),
    (166, 297, 9),
    (169, 297, 9),
    (170, 297, 9),
    (171, 297, 9),
    (15, 297, 9),
    (29, 297, 9),
    (39, 297, 9),
    (54, 297, 9),
    (56, 297, 9),
    (81, 286, 9),
    (81, 287, 9),
    (81, 288, 9),
    (81, 298, 9),
    (81, 319, 9),
    (81, 327, 9),
    (81, 328, 9),
    (81, 172, 9),
    (81, 174, 9),
    (81, 177, 9),
    (81, 184, 9),
    (81, 200, 9),
    (81, 204, 9),
    (81, 210, 9),
    (81, 217, 9),
    (81, 218, 9),
    (81, 219, 9),
    (81, 225, 9),
    (81, 229, 9),
    (81, 240, 9),
    (81, 244, 9),
    (81, 254, 9),
    (81, 257, 9),
    (149, 265, 9),
    (145, 202, 9),
    (147, 297, 9),
    (160, 297, 9),
    (145, 286, 9),
    (145, 287, 9),
    (145, 288, 9),
    (145, 298, 9),
    (145, 318, 9),
    (145, 172, 9),
    (145, 174, 9),
    (145, 177, 9),
    (145, 184, 9),
    (145, 200, 9),
    (145, 204, 9),
    (145, 210, 9),
    (145, 217, 9),
    (145, 218, 9),
    (145, 219, 9),
    (145, 225, 9),
    (145, 229, 9),
    (145, 236, 9),
    (145, 240, 9),
    (145, 244, 9),
    (145, 254, 9),
    (145, 257, 9),
    (145, 265, 9),
    (90, 297, 9),
    (128, 297, 9),
    (154, 297, 9),
    (155, 297, 9),
    (156, 297, 9),
    (167, 297, 9),
    (32, 297, 9),
    (45, 297, 9),
    (49, 297, 9),
    (51, 297, 9),
    (58, 297, 9),
    (89, 286, 9),
    (89, 287, 9),
    (89, 288, 9),
    (89, 298, 9),
    (89, 324, 9),
    (89, 327, 9),
    (89, 328, 9),
    (89, 172, 9),
    (89, 174, 9),
    (89, 177, 9),
    (89, 184, 9),
    (89, 200, 9),
    (89, 204, 9),
    (89, 210, 9),
    (89, 217, 9),
    (89, 218, 9),
    (89, 219, 9),
    (89, 225, 9),
    (89, 229, 9),
    (89, 236, 9),
    (89, 240, 9),
    (89, 244, 9),
    (89, 254, 9),
    (89, 257, 9),
    (100, 297, 9),
    (14, 286, 9),
    (14, 287, 9),
    (14, 298, 9),
    (14, 310, 9),
    (14, 319, 9),
    (14, 327, 9),
    (14, 328, 9),
    (14, 336, 9),
    (14, 172, 9),
    (14, 174, 9),
    (14, 177, 9),
    (14, 179, 9),
    (14, 184, 9),
    (14, 188, 9),
    (14, 200, 9),
    (14, 204, 9),
    (14, 208, 9),
    (14, 210, 9),
    (14, 212, 9),
    (14, 217, 9),
    (14, 218, 9),
    (14, 219, 9),
    (14, 225, 9),
    (14, 229, 9),
    (14, 240, 9),
    (14, 244, 9),
    (14, 254, 9),
    (14, 256, 9),
    (14, 257, 9),
    (111, 265, 9),
    (122, 265, 9),
    (130, 265, 9),
    (145, 206, 9),
    (147, 265, 9),
    (150, 265, 9),
    (152, 265, 9),
    (157, 265, 9),
    (158, 265, 9),
    (161, 265, 9),
    (162, 265, 9),
    (163, 265, 9),
    (169, 265, 9),
    (170, 265, 9),
    (15, 265, 9),
    (29, 265, 9),
    (54, 265, 9),
    (56, 265, 9),
    (151, 286, 9),
    (151, 298, 9),
    (151, 310, 9),
    (151, 311, 9),
    (151, 327, 9),
    (151, 328, 9),
    (151, 336, 9),
    (151, 172, 9),
    (151, 174, 9),
    (151, 179, 9),
    (151, 184, 9),
    (151, 188, 9),
    (151, 200, 9),
    (151, 208, 9),
    (151, 210, 9),
    (151, 212, 9),
    (151, 219, 9),
    (151, 240, 9),
    (151, 244, 9),
    (151, 254, 9),
    (151, 256, 9),
    (151, 257, 9),
    (111, 263, 9),
    (122, 263, 9),
    (130, 263, 9),
    (150, 263, 9),
    (152, 263, 9),
    (157, 263, 9),
    (158, 263, 9),
    (161, 263, 9),
    (163, 263, 9),
    (169, 263, 9),
    (170, 263, 9),
    (15, 263, 9),
    (29, 263, 9),
    (54, 263, 9),
    (56, 263, 9),
    (81, 310, 9),
    (81, 336, 9),
    (81, 179, 9),
    (81, 188, 9),
    (81, 208, 9),
    (81, 212, 9),
    (81, 256, 9),
    (89, 206, 9),
    (147, 263, 9),
    (160, 263, 9),
    (93, 286, 9),
    (93, 287, 9),
    (93, 298, 9),
    (93, 310, 9),
    (93, 324, 9),
    (93, 327, 9),
    (93, 328, 9),
    (93, 336, 9),
    (93, 172, 9),
    (93, 174, 9),
    (93, 177, 9),
    (93, 179, 9),
    (93, 184, 9),
    (93, 188, 9),
    (93, 200, 9),
    (93, 204, 9),
    (93, 208, 9),
    (93, 210, 9),
    (93, 212, 9),
    (93, 217, 9),
    (93, 218, 9),
    (93, 219, 9),
    (93, 225, 9),
    (93, 229, 9),
    (93, 236, 9),
    (93, 240, 9),
    (93, 244, 9),
    (93, 254, 9),
    (93, 256, 9),
    (93, 257, 9),
    (90, 263, 9),
    (100, 263, 9),
    (154, 263, 9),
    (167, 263, 9),
    (32, 263, 9),
    (45, 263, 9),
    (49, 263, 9),
    (51, 263, 9),
    (58, 263, 9),
    (145, 263, 8),
    (145, 263, 18),
    (145, 263, 20),
    (145, 263, 22),
    (145, 263, 3),
    (145, 263, 29),
    (145, 263, 25),
    (145, 286, 32),
    (145, 287, 32),
    (145, 298, 32),
    (145, 310, 32),
    (145, 318, 32),
    (145, 336, 32),
    (145, 172, 32),
    (145, 174, 32),
    (145, 177, 32),
    (145, 179, 32),
    (145, 184, 32),
    (145, 188, 32),
    (145, 200, 32),
    (145, 204, 32),
    (145, 208, 32),
    (145, 210, 32),
    (145, 212, 32),
    (145, 217, 32),
    (145, 218, 32),
    (145, 219, 32),
    (145, 225, 32),
    (145, 229, 32),
    (145, 236, 32),
    (145, 240, 32),
    (145, 244, 32),
    (145, 254, 32),
    (145, 256, 32),
    (145, 257, 32),
    (90, 263, 32),
    (111, 263, 32),
    (122, 263, 32),
    (128, 263, 32),
    (130, 263, 32),
    (147, 263, 32),
    (150, 263, 32),
    (152, 263, 32),
    (154, 263, 32),
    (155, 263, 32),
    (156, 263, 32),
    (157, 263, 32),
    (158, 263, 32),
    (160, 263, 32),
    (161, 263, 32),
    (163, 263, 32),
    (167, 263, 32),
    (169, 263, 32),
    (170, 263, 32),
    (15, 263, 32),
    (29, 263, 32),
    (32, 263, 32),
    (45, 263, 32),
    (49, 263, 32),
    (51, 263, 32),
    (54, 263, 32),
    (56, 263, 32),
    (58, 263, 32),
    (100, 265, 9),
    (101, 265, 9),
    (154, 265, 9),
    (167, 265, 9),
    (32, 265, 9),
    (45, 265, 9),
    (49, 265, 9),
    (51, 265, 9),
    (58, 265, 9),
    (137, 286, 9),
    (137, 298, 9),
    (137, 310, 9),
    (137, 311, 9),
    (11, 327, 9),
    (11, 328, 9),
    (137, 336, 9),
    (137, 172, 9),
    (137, 174, 9),
    (137, 175, 9),
    (137, 179, 9),
    (137, 184, 9),
    (137, 188, 9),
    (137, 189, 9),
    (137, 200, 9),
    (137, 208, 9),
    (137, 210, 9),
    (137, 212, 9),
    (137, 219, 9),
    (137, 227, 9),
    (137, 240, 9),
    (137, 244, 9),
    (137, 254, 9),
    (137, 256, 9),
    (137, 257, 9),
    (81, 299, 9),
    (96, 299, 9),
    (111, 299, 9),
    (122, 299, 9),
    (130, 299, 9),
    (135, 299, 9),
    (145, 299, 9),
    (149, 299, 9),
    (150, 299, 9),
    (152, 299, 9),
    (157, 299, 9),
    (158, 299, 9),
    (161, 299, 9),
    (163, 299, 9),
    (169, 299, 9),
    (170, 299, 9),
    (15, 299, 9),
    (29, 299, 9),
    (46, 299, 9),
    (54, 299, 9),
    (56, 299, 9),
    (11, 286, 9),
    (11, 306, 9),
    (11, 310, 9),
    (11, 336, 9),
    (11, 172, 9),
    (11, 174, 9),
    (11, 175, 9),
    (11, 179, 9),
    (11, 184, 9),
    (11, 188, 9),
    (11, 189, 9),
    (11, 200, 9),
    (11, 208, 9),
    (11, 210, 9),
    (11, 212, 9),
    (11, 219, 9),
    (11, 227, 9),
    (11, 244, 9),
    (11, 254, 9),
    (11, 256, 9),
    (11, 257, 9),
    (72, 250, 9),
    (96, 250, 9),
    (111, 250, 9),
    (122, 250, 9),
    (135, 250, 9),
    (145, 250, 9),
    (149, 250, 9),
    (150, 250, 9),
    (158, 250, 9),
    (163, 250, 9),
    (170, 250, 9),
    (15, 250, 9),
    (46, 250, 9),
    (54, 250, 9),
    (43, 305, 9),
    (8, 310, 9),
    (8, 325, 9),
    (8, 328, 9),
    (8, 336, 9),
    (8, 172, 9),
    (43, 174, 9),
    (43, 179, 9),
    (8, 184, 9),
    (43, 188, 9),
    (43, 200, 9),
    (43, 208, 9),
    (8, 210, 9),
    (8, 212, 9),
    (8, 234, 9),
    (8, 239, 9),
    (8, 254, 9),
    (43, 256, 9),
    (8, 257, 9),
    (122, 237, 9),
    (125, 237, 9),
    (138, 237, 9),
    (142, 237, 9),
    (145, 183, 9),
    (149, 237, 9),
    (150, 237, 9),
    (163, 237, 9),
    (165, 237, 9),
    (168, 237, 9),
    (16, 237, 9),
    (54, 237, 9),
    (57, 237, 9),
    (124, 310, 9),
    (124, 328, 9),
    (124, 332, 9),
    (124, 336, 9),
    (124, 172, 9),
    (43, 175, 9),
    (124, 184, 9),
    (43, 189, 9),
    (124, 210, 9),
    (124, 212, 9),
    (124, 227, 9),
    (124, 234, 9),
    (124, 239, 9),
    (124, 254, 9),
    (124, 257, 9),
    (96, 296, 9),
    (122, 296, 9),
    (125, 296, 9),
    (129, 296, 9),
    (135, 296, 9),
    (138, 296, 9),
    (142, 296, 9),
    (149, 296, 9),
    (150, 296, 9),
    (163, 296, 9),
    (165, 296, 9),
    (168, 296, 9),
    (16, 296, 9),
    (46, 296, 9),
    (54, 296, 9),
    (57, 296, 9),
    (70, 286, 9),
    (70, 306, 9),
    (70, 310, 9),
    (70, 325, 9),
    (70, 328, 9),
    (70, 336, 9),
    (70, 172, 9),
    (70, 174, 9),
    (70, 179, 9),
    (70, 184, 9),
    (70, 188, 9),
    (70, 200, 9),
    (70, 208, 9),
    (70, 210, 9),
    (70, 212, 9),
    (70, 219, 9),
    (70, 234, 9),
    (70, 239, 9),
    (70, 244, 9),
    (70, 254, 9),
    (70, 256, 9),
    (70, 257, 9),
    (72, 296, 9),
    (111, 237, 9),
    (145, 296, 9),
    (158, 237, 9),
    (170, 237, 9),
    (15, 237, 9),
    (70, 332, 9),
    (70, 175, 9),
    (70, 189, 9),
    (70, 227, 9),
    (111, 296, 9),
    (158, 296, 9),
    (170, 296, 9),
    (15, 296, 9),
    (8, 317, 9),
    (8, 332, 9),
    (8, 174, 9),
    (8, 175, 9),
    (8, 179, 9),
    (8, 188, 9),
    (8, 189, 9),
    (8, 208, 9),
    (8, 227, 9),
    (8, 256, 9),
    (68, 327, 9),
    (96, 327, 9),
    (125, 327, 9),
    (129, 327, 9),
    (135, 327, 9),
    (138, 327, 9),
    (142, 327, 9),
    (145, 327, 9),
    (165, 327, 9),
    (168, 327, 9),
    (16, 327, 9),
    (46, 327, 9),
    (57, 327, 9),
    (43, 309, 9),
    (6, 173, 9),
    (43, 182, 9),
    (6, 184, 9),
    (43, 196, 9),
    (43, 198, 9),
    (43, 207, 9),
    (144, 223, 9),
    (44, 226, 9),
    (44, 246, 9),
    (108, 222, 9),
    (118, 222, 9),
    (134, 222, 9),
    (140, 222, 9),
    (145, 190, 9),
    (148, 222, 9),
    (31, 222, 9),
    (47, 222, 9),
    (55, 222, 9),
    (43, 190, 7),
    (43, 309, 15),
    (109, 173, 15),
    (43, 174, 15),
    (43, 178, 15),
    (109, 184, 15),
    (43, 196, 15),
    (43, 198, 15),
    (43, 207, 15),
    (109, 223, 15),
    (43, 226, 15),
    (43, 246, 15),
    (108, 190, 15),
    (118, 190, 15),
    (134, 190, 15),
    (140, 190, 15),
    (145, 190, 15),
    (148, 190, 15),
    (31, 190, 15),
    (47, 190, 15),
    (55, 190, 15),
    (109, 190, 19),
    (43, 304, 9),
    (77, 310, 9),
    (43, 326, 9),
    (77, 173, 9),
    (77, 184, 9),
    (43, 212, 9),
    (77, 223, 9),
    (77, 226, 9),
    (77, 246, 9),
    (145, 232, 9),
    (149, 222, 9),
    (119, 222, 8),
    (119, 290, 19),
    (119, 292, 19),
    (119, 304, 19),
    (119, 310, 19),
    (119, 325, 19),
    (119, 173, 19),
    (119, 174, 19),
    (119, 179, 19),
    (119, 184, 19),
    (119, 188, 19),
    (119, 196, 19),
    (119, 207, 19),
    (119, 208, 19),
    (119, 212, 19),
    (119, 234, 19),
    (119, 239, 19),
    (119, 246, 19),
    (119, 256, 19),
    (118, 222, 19),
    (124, 222, 19),
    (125, 222, 19),
    (138, 222, 19),
    (142, 222, 19),
    (145, 181, 19),
    (148, 222, 19),
    (149, 222, 19),
    (153, 222, 19),
    (165, 222, 19),
    (168, 222, 19),
    (16, 222, 19),
    (55, 222, 19),
    (57, 222, 19),
    (43, 290, 9),
    (77, 325, 9),
    (7, 234, 9),
    (7, 239, 9),
    (118, 293, 9),
    (124, 293, 9),
    (125, 293, 9),
    (138, 293, 9),
    (142, 293, 9),
    (145, 181, 9),
    (148, 293, 9),
    (149, 293, 9),
    (153, 293, 9),
    (165, 293, 9),
    (168, 293, 9),
    (16, 293, 9),
    (55, 293, 9),
    (57, 293, 9),
    (43, 292, 7),
    (43, 290, 15),
    (43, 308, 15),
    (77, 173, 15),
    (77, 184, 15),
    (77, 223, 15),
    (77, 226, 15),
    (77, 234, 15),
    (77, 239, 15),
    (77, 246, 15),
    (82, 292, 15),
    (108, 292, 15),
    (118, 292, 15),
    (125, 292, 15),
    (134, 292, 15),
    (138, 292, 15),
    (140, 292, 15),
    (142, 292, 15),
    (145, 292, 15),
    (148, 292, 15),
    (153, 292, 15),
    (165, 292, 15),
    (168, 292, 15),
    (16, 292, 15),
    (31, 292, 15),
    (47, 292, 15),
    (55, 292, 15),
    (57, 292, 15),
    (109, 292, 19),
    (68, 290, 9),
    (59, 292, 9),
    (68, 305, 9),
    (68, 310, 9),
    (68, 325, 9),
    (68, 336, 9),
    (68, 173, 9),
    (68, 174, 9),
    (68, 179, 9),
    (68, 184, 9),
    (68, 188, 9),
    (68, 196, 9),
    (68, 200, 9),
    (68, 207, 9),
    (68, 208, 9),
    (68, 210, 9),
    (68, 212, 9),
    (68, 234, 9),
    (68, 239, 9),
    (68, 246, 9),
    (68, 254, 9),
    (68, 256, 9),
    (122, 293, 9),
    (150, 293, 9),
    (163, 293, 9),
    (54, 293, 9),
    (70, 290, 9),
    (70, 292, 9),
    (70, 173, 9),
    (70, 196, 9),
    (70, 207, 9),
    (70, 246, 9),
    (72, 293, 9),
    (111, 293, 9),
    (145, 293, 9),
    (158, 293, 9),
    (170, 293, 9),
    (15, 293, 9),
    (68, 292, 9),
    (68, 326, 9),
    (68, 176, 9),
    (68, 186, 9),
    (68, 216, 9),
    (74, 232, 9),
    (118, 232, 9),
    (122, 232, 9),
    (148, 232, 9),
    (149, 232, 9),
    (159, 232, 9),
    (55, 232, 9),
    (74, 172, 9),
    (118, 172, 9),
    (122, 172, 9),
    (125, 172, 9),
    (138, 172, 9),
    (142, 172, 9),
    (148, 172, 9),
    (153, 172, 9),
    (159, 172, 9),
    (165, 172, 9),
    (168, 172, 9),
    (16, 172, 9),
    (55, 172, 9),
    (57, 172, 9),
    (43, 257, 8),
    (6, 257, 19),
    (43, 328, 8),
    (43, 328, 18),
    (6, 328, 21),
    (52, 174, 9),
    (145, 328, 9),
    (44, 290, 9),
    (7, 310, 9),
    (44, 317, 9),
    (7, 325, 9),
    (7, 173, 9),
    (44, 174, 9),
    (44, 179, 9),
    (7, 184, 9),
    (44, 188, 9),
    (44, 196, 9),
    (44, 207, 9),
    (44, 208, 9),
    (44, 212, 9),
    (7, 246, 9),
    (44, 256, 9),
    (68, 193, 9),
    (145, 193, 9),
    (44, 321, 9),
    (44, 182, 9),
    (44, 198, 9),
    (145, 191, 9),
    (44, 191, 5),
    (44, 191, 10),
    (109, 191, 12),
    (109, 191, 15),
    (109, 191, 19),
    (44, 322, 9),
    (78, 173, 9),
    (78, 184, 9),
    (78, 223, 9),
    (78, 226, 9),
    (78, 246, 9),
    (44, 322, 8),
    (78, 173, 8),
    (44, 174, 8),
    (44, 178, 8),
    (78, 184, 8),
    (44, 196, 8),
    (44, 198, 8),
    (44, 207, 8),
    (78, 223, 8),
    (44, 226, 8),
    (44, 246, 8),
    (108, 292, 8),
    (118, 292, 8),
    (134, 292, 8),
    (140, 292, 8),
    (145, 292, 8),
    (148, 292, 8),
    (31, 292, 8),
    (47, 292, 8),
    (55, 292, 8),
    (109, 327, 19),
    (77, 292, 7),
    (77, 290, 14),
    (77, 320, 14),
    (77, 173, 14),
    (77, 174, 14),
    (77, 178, 14),
    (77, 184, 14),
    (77, 196, 14),
    (77, 198, 14),
    (77, 207, 14),
    (77, 223, 14),
    (77, 226, 14),
    (77, 234, 14),
    (77, 239, 14),
    (77, 246, 14),
    (82, 292, 14),
    (108, 292, 14),
    (118, 292, 14),
    (125, 292, 14),
    (134, 292, 14),
    (138, 292, 14),
    (140, 292, 14),
    (142, 292, 14),
    (145, 292, 14),
    (148, 292, 14),
    (153, 292, 14),
    (165, 292, 14),
    (168, 292, 14),
    (16, 292, 14),
    (31, 292, 14),
    (47, 292, 14),
    (55, 292, 14),
    (57, 292, 14),
    (77, 222, 13),
    (77, 222, 1),
    (77, 222, 26),
    (77, 327, 28),
    (77, 327, 17),
    (77, 327, 19),
    (80, 290, 5),
    (80, 292, 5),
    (80, 310, 5),
    (80, 317, 5),
    (80, 325, 5),
    (80, 328, 5),
    (80, 173, 5),
    (80, 174, 5),
    (80, 179, 5),
    (80, 184, 5),
    (80, 188, 5),
    (80, 196, 5),
    (80, 207, 5),
    (80, 208, 5),
    (80, 212, 5),
    (80, 234, 5),
    (80, 239, 5),
    (80, 246, 5),
    (80, 256, 5),
    (68, 293, 5),
    (118, 293, 5),
    (124, 293, 5),
    (125, 293, 5),
    (138, 293, 5),
    (142, 293, 5),
    (145, 293, 5),
    (148, 293, 5),
    (149, 293, 5),
    (153, 293, 5),
    (165, 293, 5),
    (168, 293, 5),
    (16, 293, 5),
    (55, 293, 5),
    (57, 293, 5),
    (80, 327, 11),
    (80, 327, 15),
    (80, 327, 19),
    (52, 257, 7),
    (52, 257, 14),
    (52, 174, 17),
    (6, 184, 17),
    (84, 257, 17),
    (145, 257, 17),
    (44, 257, 17),
    (144, 289, 9),
    (43, 307, 9),
    (43, 180, 9),
    (144, 184, 9),
    (43, 201, 9),
    (43, 205, 9),
    (43, 228, 9),
    (144, 230, 9),
    (78, 291, 9),
    (86, 291, 9),
    (109, 291, 9),
    (120, 291, 9),
    (132, 291, 9),
    (134, 291, 9),
    (140, 291, 9),
    (145, 291, 9),
    (146, 291, 9),
    (31, 291, 9),
    (47, 291, 9),
    (44, 295, 9),
    (44, 184, 9),
    (44, 215, 9),
    (44, 223, 9),
    (44, 230, 9),
    (78, 257, 9),
    (107, 291, 9),
    (136, 291, 9),
    (164, 291, 9),
    (18, 291, 9),
    (50, 291, 9),
    (43, 184, 9),
    (43, 291, 8),
    (43, 197, 18),
    (144, 197, 21),
    (84, 295, 9),
    (43, 303, 9),
    (84, 184, 9),
    (84, 215, 9),
    (84, 230, 9),
    (98, 291, 9),
    (43, 328, 20),
    (144, 328, 23),
    (52, 184, 9),
    (44, 257, 8),
    (44, 197, 18),
    (44, 197, 20),
    (44, 197, 22),
    (44, 197, 2),
    (44, 327, 4),
    (44, 197, 29),
    (44, 295, 31),
    (44, 314, 31),
    (44, 174, 31),
    (44, 184, 31),
    (44, 215, 31),
    (44, 230, 31),
    (79, 197, 31),
    (107, 197, 31),
    (132, 197, 31),
    (136, 197, 31),
    (145, 197, 31),
    (146, 197, 31),
    (164, 197, 31),
    (18, 197, 31),
    (50, 197, 31),
    (80, 197, 9),
    (44, 291, 8),
    (84, 291, 8),
    (144, 289, 19),
    (44, 321, 19),
    (44, 174, 19),
    (44, 180, 19),
    (44, 182, 19),
    (144, 184, 19),
    (44, 198, 19),
    (44, 201, 19),
    (44, 205, 19),
    (144, 223, 19),
    (44, 226, 19),
    (44, 228, 19),
    (144, 230, 19),
    (78, 291, 19),
    (86, 291, 19),
    (109, 291, 19),
    (120, 291, 19),
    (132, 291, 19),
    (134, 291, 19),
    (140, 291, 19),
    (145, 291, 19),
    (146, 291, 19),
    (31, 291, 19),
    (47, 291, 19),
    (44, 257, 18),
    (84, 295, 21),
    (44, 321, 21),
    (44, 174, 21),
    (44, 182, 21),
    (84, 184, 21),
    (44, 198, 21),
    (84, 215, 21),
    (84, 223, 21),
    (84, 226, 21),
    (84, 230, 21),
    (78, 257, 21),
    (86, 257, 21),
    (107, 257, 21),
    (109, 257, 21),
    (132, 257, 21),
    (134, 257, 21),
    (136, 257, 21),
    (140, 257, 21),
    (145, 257, 21),
    (146, 257, 21),
    (164, 257, 21),
    (18, 257, 21),
    (31, 257, 21),
    (47, 257, 21),
    (50, 257, 21),
    (84, 174, 19),
    (9, 184, 19),
    (80, 328, 19),
    (84, 312, 19),
    (84, 180, 19),
    (84, 201, 19),
    (84, 205, 19),
    (84, 228, 19),
    (9, 230, 19),
    (98, 257, 19),
    (120, 257, 19),
    (132, 257, 19),
    (145, 257, 19),
    (146, 257, 19),
    (84, 295, 19),
    (84, 314, 19),
    (84, 184, 19),
    (84, 215, 19),
    (84, 230, 19),
    (98, 294, 19),
    (107, 294, 19),
    (132, 294, 19),
    (136, 294, 19),
    (145, 294, 19),
    (146, 294, 19),
    (164, 294, 19),
    (18, 294, 19),
    (50, 294, 19),
    (80, 294, 19)
  ]

private def pathKeys : List PKey :=
  [
    (false, [8, 11, 12, 14, 17, 52, 137, 149, 258, 259], [1, 2, 12, 13, 40, 43, 44, 59, 61, 64, 71, 87, 91, 97, 104, 105, 106, 112, 116, 123, 127, 131, 137, 141, 144, 151, 203, 213, 224, 235, 243, 259, 261, 264, 266, 268, 271, 272, 274, 275, 281, 283, 284, 300, 313, 316, 329, 333, 335, 337, 339, 341], [(1, some 1), (2, some 2), (12, none), (13, some 3), (40, some 4), (43, some 5), (44, some 6), (59, some 7), (61, some 8), (64, some 9), (71, some 10), (87, some 11), (91, some 12), (97, some 13), (104, some 14), (105, some 15), (106, some 16), (112, some 17), (116, some 18), (123, some 19), (127, some 20), (131, some 21), (137, none), (141, some 22), (144, some 23), (151, some 24), (203, some 25), (213, some 26), (224, some 27), (235, some 28), (243, some 29), (259, none), (261, some 30), (264, some 31), (266, some 32), (268, some 33), (271, some 34), (272, some 35), (274, some 36), (275, some 37), (281, some 38), (283, some 39), (284, some 40), (300, some 41), (313, some 42), (316, some 43), (329, some 44), (333, some 45), (335, some 46), (337, some 47), (339, some 48), (341, some 49)]),
    (false, [8, 11, 14, 17, 52, 137, 149, 194, 258, 297], [1, 3, 13, 14, 27, 43, 44, 59, 61, 71, 87, 97, 106, 127, 131, 137, 141, 144, 149, 194, 224, 235, 243, 252, 259, 264, 266, 271, 272, 275, 277, 280, 283, 284, 285, 300, 313, 323, 337, 339], [(1, some 57), (3, some 58), (13, some 59), (14, none), (27, some 60), (43, some 61), (44, some 62), (59, some 63), (61, some 64), (71, some 65), (87, some 66), (97, some 67), (106, some 68), (127, some 69), (131, some 70), (137, none), (141, some 71), (144, some 72), (149, none), (194, none), (224, some 73), (235, some 74), (243, some 75), (252, some 76), (259, some 77), (264, some 78), (266, some 79), (271, some 80), (272, some 81), (275, some 82), (277, some 83), (280, some 84), (283, some 85), (284, some 86), (285, some 87), (300, some 88), (313, some 89), (323, some 90), (337, some 91), (339, some 92)]),
    (false, [8, 11, 14, 17, 52, 81, 137, 149, 202, 258, 297], [1, 2, 3, 13, 14, 35, 43, 44, 59, 61, 64, 71, 87, 91, 97, 104, 105, 106, 112, 116, 127, 131, 137, 141, 144, 149, 151, 202, 224, 235, 243, 252, 259, 261, 264, 266, 271, 272, 274, 275, 277, 280, 283, 284, 285, 300, 313, 323, 337, 339], [(1, some 93), (2, some 94), (3, some 95), (13, some 96), (14, none), (35, some 97), (43, some 98), (44, some 99), (59, some 100), (61, some 101), (64, some 102), (71, some 103), (87, some 104), (91, some 105), (97, some 106), (104, some 107), (105, some 108), (106, some 109), (112, some 110), (116, some 111), (127, some 112), (131, some 113), (137, none), (141, some 114), (144, some 115), (149, none), (151, some 116), (202, none), (224, some 73), (235, some 74), (243, some 75), (252, some 76), (259, some 117), (261, some 118), (264, some 78), (266, some 79), (271, some 80), (272, some 81), (274, some 119), (275, some 82), (277, some 83), (280, some 84), (283, some 85), (284, some 86), (285, some 87), (300, some 88), (313, some 89), (323, some 90), (337, some 91), (339, some 92)]),
    (false, [8, 11, 14, 17, 52, 81, 89, 137, 145, 149, 258, 297], [1, 2, 3, 13, 14, 34, 59, 61, 64, 71, 87, 91, 97, 104, 105, 106, 112, 116, 123, 127, 131, 137, 141, 144, 145, 149, 151, 203, 224, 235, 241, 243, 252, 261, 264, 266, 268, 269, 270, 271, 272, 274, 275, 277, 280, 281, 283, 284, 285, 300, 313, 316, 323, 329, 333, 335, 337, 339, 341], [(1, some 120), (2, some 121), (3, some 122), (13, some 123), (14, none), (34, some 124), (59, some 125), (61, some 126), (64, some 127), (71, some 128), (87, some 129), (91, some 130), (97, some 131), (104, some 132), (105, some 133), (106, some 134), (112, some 135), (116, some 136), (123, some 137), (127, some 138), (131, some 139), (137, none), (141, some 140), (144, some 141), (145, none), (149, none), (151, some 142), (203, some 143), (224, some 73), (235, some 74), (241, some 144), (243, some 75), (252, some 76), (261, some 118), (264, some 78), (266, some 79), (268, some 145), (269, some 146), (270, some 147), (271, some 80), (272, some 81), (274, some 119), (275, some 82), (277, some 83), (280, some 84), (281, some 148), (283, some 85), (284, some 86), (285, some 87), (300, some 88), (313, some 89), (316, some 149), (323, some 90), (329, some 150), (333, some 151), (335, some 152), (337, some 91), (339, some 92), (341, some 153)]),
    (false, [8, 11, 14, 17, 52, 81, 89, 137, 149, 258, 259, 297], [1, 2, 3, 13, 14, 40, 43, 44, 59, 61, 64, 71, 87, 91, 97, 104, 105, 106, 112, 116, 123, 127, 131, 137, 141, 144, 149, 151, 203, 213, 224, 235, 243, 252, 259, 261, 264, 266, 268, 271, 272, 274, 275, 277, 280, 281, 283, 284, 285, 300, 313, 316, 323, 329, 333, 335, 337, 339, 341], [(1, some 154), (2, some 155), (3, some 156), (13, some 157), (14, none), (40, some 158), (43, some 159), (44, some 160), (59, some 161), (61, some 162), (64, some 163), (71, some 164), (87, some 165), (91, some 166), (97, some 167), (104, some 168), (105, some 169), (106, some 170), (112, some 171), (116, some 172), (123, some 173), (127, some 174), (131, some 175), (137, none), (141, some 176), (144, some 177), (149, none), (151, some 116), (203, some 143), (213, some 178), (224, some 73), (235, some 74), (243, some 75), (252, some 76), (259, none), (261, some 118), (264, some 78), (266, some 79), (268, some 145), (271, some 80), (272, some 81), (274, some 119), (275, some 82), (277, some 83), (280, some 84), (281, some 148), (283, some 85), (284, some 86), (285, some 87), (300, some 88), (313, some 89), (316, some 149), (323, some 90), (329, some 150), (333, some 151), (335, some 152), (337, some 91), (339, some 92), (341, some 153)]),
    (false, [8, 11, 14, 17, 52, 137, 206, 258, 263, 265], [1, 2, 13, 14, 26, 35, 43, 44, 53, 59, 61, 64, 66, 71, 75, 87, 91, 95, 97, 99, 104, 105, 106, 112, 116, 127, 131, 137, 141, 143, 144, 206, 224, 235, 243, 259, 261, 263, 264, 265, 266, 271, 272, 275, 276, 277, 283, 284, 300, 313, 337, 339], [(1, some 179), (2, some 180), (13, some 181), (14, none), (26, some 182), (35, some 183), (43, some 184), (44, some 185), (53, some 186), (59, some 187), (61, some 188), (64, some 189), (66, some 190), (71, some 191), (75, some 192), (87, some 193), (91, some 194), (95, some 195), (97, some 196), (99, some 197), (104, some 198), (105, some 199), (106, some 200), (112, some 201), (116, some 202), (127, some 203), (131, some 204), (137, none), (141, some 205), (143, some 206), (144, some 207), (206, none), (224, some 208), (235, some 209), (243, some 210), (259, some 211), (261, some 212), (263, none), (264, some 213), (265, none), (266, some 214), (271, some 215), (272, some 216), (275, some 217), (276, some 218), (277, some 219), (283, some 220), (284, some 221), (300, some 222), (313, some 223), (337, some 224), (339, some 225)]),
    (false, [8, 11, 14, 17, 52, 137, 151, 194, 206, 258, 263], [1, 13, 14, 26, 27, 43, 44, 53, 59, 61, 66, 71, 75, 87, 95, 97, 99, 106, 127, 131, 137, 141, 143, 144, 194, 224, 235, 243, 259, 263, 264, 266, 271, 272, 275, 277, 283, 284, 300, 313, 337, 339], [(1, some 226), (13, some 227), (14, none), (26, some 228), (27, some 229), (43, some 230), (44, some 231), (53, some 232), (59, some 233), (61, some 234), (66, some 235), (71, some 236), (75, some 237), (87, some 238), (95, some 239), (97, some 240), (99, some 241), (106, some 242), (127, some 243), (131, some 244), (137, none), (141, some 245), (143, some 246), (144, some 247), (194, none), (224, some 248), (235, some 249), (243, some 250), (259, some 77), (263, none), (264, some 251), (266, some 252), (271, some 253), (272, some 254), (275, some 255), (277, some 256), (283, some 257), (284, some 258), (300, some 259), (313, some 260), (337, some 261), (339, some 262)]),
    (false, [8, 11, 14, 17, 52, 81, 137, 151, 206, 258, 263], [1, 2, 13, 14, 26, 35, 43, 44, 53, 59, 61, 64, 66, 71, 75, 87, 91, 95, 97, 99, 104, 105, 106, 112, 116, 127, 131, 137, 141, 143, 144, 151, 202, 224, 235, 243, 259, 261, 263, 264, 266, 271, 272, 274, 275, 277, 283, 284, 300, 313, 337, 339], [(1, some 93), (2, some 94), (13, some 96), (14, none), (26, some 263), (35, some 97), (43, some 98), (44, some 99), (53, some 264), (59, some 100), (61, some 101), (64, some 102), (66, some 265), (71, some 103), (75, some 266), (87, some 104), (91, some 105), (95, some 267), (97, some 106), (99, some 268), (104, some 107), (105, some 108), (106, some 109), (112, some 110), (116, some 111), (127, some 112), (131, some 113), (137, none), (141, some 114), (143, some 269), (144, some 115), (151, none), (202, some 270), (224, some 248), (235, some 249), (243, some 250), (259, some 211), (261, some 271), (263, none), (264, some 251), (266, some 252), (271, some 253), (272, some 254), (274, some 272), (275, some 255), (277, some 256), (283, some 257), (284, some 258), (300, some 259), (313, some 260), (337, some 261), (339, some 262)]),
    (false, [8, 11, 14, 17, 52, 93, 137, 151, 258, 259, 263], [1, 2, 13, 14, 26, 40, 43, 44, 53, 59, 61, 64, 66, 71, 75, 87, 91, 95, 97, 99, 104, 105, 106, 112, 116, 123, 127, 131, 137, 141, 143, 144, 151, 203, 213, 224, 235, 243, 259, 261, 263, 264, 266, 268, 271, 272, 274, 275, 277, 281, 283, 284, 300, 313, 316, 329, 333, 335, 337, 339, 341], [(1, some 273), (2, some 274), (13, some 275), (14, none), (26, some 276), (40, some 277), (43, some 278), (44, some 279), (53, some 280), (59, some 281), (61, some 282), (64, some 283), (66, some 284), (71, some 285), (75, some 286), (87, some 287), (91, some 288), (95, some 289), (97, some 290), (99, some 291), (104, some 292), (105, some 293), (106, some 294), (112, some 295), (116, some 296), (123, some 297), (127, some 298), (131, some 299), (137, none), (141, some 300), (143, some 301), (144, some 302), (151, none), (203, some 303), (213, some 304), (224, some 248), (235, some 249), (243, some 250), (259, none), (261, some 271), (263, none), (264, some 251), (266, some 252), (268, some 305), (271, some 253), (272, some 254), (274, some 272), (275, some 255), (277, some 256), (281, some 306), (283, some 257), (284, some 258), (300, some 259), (313, some 260), (316, some 307), (329, some 308), (333, some 309), (335, some 310), (337, some 261), (339, some 262), (341, some 311)]),
    (false, [8, 11, 14, 17, 52, 93, 137, 145, 151, 258, 263], [1, 2, 13, 14, 26, 34, 53, 59, 61, 64, 66, 71, 75, 87, 91, 95, 97, 99, 104, 105, 106, 112, 116, 123, 127, 131, 137, 141, 143, 144, 145, 151, 203, 224, 235, 241, 243, 261, 263, 264, 266, 268, 269, 270, 271, 272, 274, 275, 277, 281, 283, 284, 300, 313, 316, 329, 333, 335, 337, 339, 341], [(1, some 319), (2, some 320), (13, some 321), (14, none), (26, some 322), (34, some 323), (53, some 324), (59, some 325), (61, some 326), (64, some 327), (66, some 328), (71, some 329), (75, some 330), (87, some 331), (91, some 332), (95, some 333), (97, some 334), (99, some 335), (104, some 336), (105, some 337), (106, some 338), (112, some 339), (116, some 340), (123, some 341), (127, some 342), (131, some 343), (137, none), (141, some 344), (143, some 345), (144, some 346), (145, none), (151, none), (203, some 347), (224, some 348), (235, some 349), (241, some 350), (243, some 351), (261, some 352), (263, none), (264, some 353), (266, some 354), (268, some 355), (269, some 356), (270, some 357), (271, some 358), (272, some 359), (274, some 360), (275, some 361), (277, some 362), (281, some 363), (283, some 364), (284, some 365), (300, some 366), (313, some 367), (316, some 368), (329, some 369), (333, some 370), (335, some 371), (337, some 372), (339, some 373), (341, some 374)]),
    (false, [8, 11, 14, 17, 52, 93, 137, 258, 263, 265], [1, 2, 13, 14, 26, 40, 43, 44, 53, 59, 61, 64, 66, 71, 75, 87, 91, 95, 97, 99, 104, 105, 106, 112, 116, 123, 127, 131, 137, 141, 143, 144, 213, 214, 224, 235, 243, 259, 261, 263, 264, 265, 266, 268, 271, 272, 275, 276, 277, 281, 283, 284, 300, 313, 316, 329, 333, 335, 337, 339, 341], [(1, some 273), (2, some 274), (13, some 275), (14, none), (26, some 276), (40, some 277), (43, some 278), (44, some 279), (53, some 280), (59, some 281), (61, some 282), (64, some 283), (66, some 284), (71, some 285), (75, some 286), (87, some 287), (91, some 288), (95, some 289), (97, some 290), (99, some 291), (104, some 292), (105, some 293), (106, some 294), (112, some 295), (116, some 296), (123, some 297), (127, some 298), (131, some 299), (137, none), (141, some 300), (143, some 301), (144, some 302), (213, some 375), (214, some 376), (224, some 208), (235, some 209), (243, some 210), (259, some 142), (261, some 212), (263, none), (264, some 213), (265, none), (266, some 214), (268, some 377), (271, some 215), (272, some 216), (275, some 217), (276, some 218), (277, some 219), (281, some 378), (283, some 220), (284, some 221), (300, some 222), (313, some 223), (316, some 379), (329, some 380), (333, some 381), (335, some 382), (337, some 224), (339, some 225), (341, some 383)]),
    (false, [8, 11, 17, 52, 137, 258, 299], [1, 11, 13, 26, 27, 43, 44, 53, 59, 61, 62, 66, 71, 75, 76, 87, 95, 97, 99, 106, 114, 127, 131, 137, 141, 143, 144, 194, 209, 224, 235, 243, 248, 259, 263, 264, 266, 271, 272, 275, 277, 283, 284, 300, 313, 330, 337, 339], [(1, some 384), (11, none), (13, some 385), (26, some 386), (27, some 387), (43, some 388), (44, some 389), (53, some 390), (59, some 391), (61, some 392), (62, some 393), (66, some 394), (71, some 395), (75, some 396), (76, some 397), (87, some 398), (95, some 399), (97, some 400), (99, some 401), (106, some 402), (114, some 403), (127, some 404), (131, some 405), (137, none), (141, some 406), (143, some 407), (144, some 408), (194, some 409), (209, some 410), (224, some 411), (235, some 412), (243, some 413), (248, some 414), (259, some 415), (263, some 416), (264, some 417), (266, some 418), (271, some 419), (272, some 420), (275, some 421), (277, some 422), (283, some 423), (284, some 424), (300, some 425), (313, some 426), (330, some 427), (337, some 428), (339, some 429)]),
    (false, [8, 11, 17, 52, 250, 258], [1, 11, 22, 26, 43, 44, 53, 59, 61, 62, 66, 71, 75, 76, 87, 95, 97, 99, 106, 114, 131, 141, 143, 144, 185, 209, 224, 235, 248, 259, 263, 264, 272, 277, 284, 300, 330, 337], [(1, some 430), (11, none), (22, some 431), (26, some 432), (43, some 388), (44, some 389), (53, some 433), (59, some 434), (61, some 435), (62, some 436), (66, some 437), (71, some 438), (75, some 439), (76, some 440), (87, some 441), (95, some 442), (97, some 443), (99, some 444), (106, some 445), (114, some 446), (131, some 447), (141, some 448), (143, some 449), (144, some 450), (185, some 451), (209, some 452), (224, some 453), (235, some 454), (248, some 455), (259, some 456), (263, some 457), (264, some 458), (272, some 459), (277, some 460), (284, some 461), (300, some 462), (330, some 463), (337, some 464)]),
    (false, [8, 17, 43, 52, 183, 237, 258, 296], [8, 21, 26, 41, 43, 44, 53, 59, 61, 66, 71, 75, 87, 95, 97, 99, 121, 126, 141, 143, 144, 183, 235, 237, 238, 251, 255, 259, 263, 264, 277, 279, 282, 301, 337, 340], [(8, none), (21, some 465), (26, some 466), (41, some 467), (43, none), (44, some 468), (53, some 469), (59, some 470), (61, some 471), (66, some 472), (71, some 473), (75, some 474), (87, some 475), (95, some 476), (97, some 477), (99, some 478), (121, some 479), (126, some 480), (141, some 481), (143, some 482), (144, some 483), (183, none), (235, some 484), (237, none), (238, some 485), (251, some 486), (255, some 487), (259, some 488), (263, some 489), (264, some 490), (277, some 491), (279, some 492), (282, some 493), (301, some 494), (337, some 495), (340, some 496)]),
    (false, [8, 17, 43, 52, 124, 183, 258, 296], [8, 21, 26, 43, 44, 48, 53, 59, 61, 62, 66, 71, 75, 76, 87, 95, 97, 99, 114, 121, 126, 141, 143, 144, 183, 209, 235, 238, 242, 248, 251, 255, 259, 263, 264, 277, 279, 282, 301, 330, 337, 340], [(8, none), (21, some 465), (26, some 497), (43, none), (44, some 498), (48, some 499), (53, some 500), (59, some 501), (61, some 471), (62, some 502), (66, some 472), (71, some 503), (75, some 474), (76, some 504), (87, some 475), (95, some 476), (97, some 505), (99, some 506), (114, some 507), (121, some 508), (126, some 509), (141, some 510), (143, some 482), (144, some 511), (183, none), (209, some 512), (235, some 513), (238, some 514), (242, some 515), (248, some 516), (251, some 517), (255, some 518), (259, some 488), (263, some 519), (264, some 520), (277, some 521), (279, some 522), (282, some 523), (301, some 524), (330, some 525), (337, some 526), (340, some 527)]),
    (false, [8, 17, 43, 52, 70, 237, 258, 296], [1, 8, 22, 26, 41, 43, 44, 53, 59, 61, 66, 71, 75, 87, 95, 97, 99, 106, 121, 126, 131, 141, 143, 144, 185, 224, 235, 237, 238, 251, 255, 259, 263, 264, 272, 277, 279, 282, 284, 300, 301, 337, 340], [(1, some 528), (8, none), (22, some 529), (26, some 530), (41, some 531), (43, none), (44, some 532), (53, some 533), (59, some 534), (61, some 535), (66, some 536), (71, some 537), (75, some 538), (87, some 539), (95, some 540), (97, some 541), (99, some 542), (106, some 543), (121, some 544), (126, some 545), (131, some 546), (141, some 547), (143, some 548), (144, some 549), (185, some 550), (224, some 551), (235, some 484), (237, none), (238, some 485), (251, some 486), (255, some 487), (259, some 552), (263, some 489), (264, some 490), (272, some 553), (277, some 491), (279, some 492), (282, some 493), (284, some 554), (300, some 555), (301, some 494), (337, some 495), (340, some 496)]),
    (false, [8, 17, 43, 52, 70, 124, 258, 296], [1, 8, 22, 26, 43, 44, 48, 53, 59, 61, 62, 66, 71, 75, 76, 87, 95, 97, 99, 106, 114, 121, 126, 131, 141, 143, 144, 185, 209, 224, 235, 238, 242, 248, 251, 255, 259, 263, 264, 272, 277, 279, 282, 284, 300, 301, 330, 337, 340], [(1, some 528), (8, none), (22, some 529), (26, some 530), (43, none), (44, some 532), (48, some 556), (53, some 533), (59, some 534), (61, some 535), (62, some 557), (66, some 536), (71, some 537), (75, some 538), (76, some 558), (87, some 539), (95, some 540), (97, some 541), (99, some 542), (106, some 543), (114, some 559), (121, some 544), (126, some 545), (131, some 546), (141, some 547), (143, some 548), (144, some 549), (185, some 550), (209, some 512), (224, some 560), (235, some 513), (238, some 514), (242, some 515), (248, some 516), (251, some 517), (255, some 518), (259, some 552), (263, some 519), (264, some 520), (272, some 561), (277, some 521), (279, some 522), (282, some 523), (284, some 562), (300, some 563), (301, some 524), (330, some 525), (337, some 526), (340, some 527)]),
    (false, [8, 17, 52, 258, 296, 327], [8, 26, 33, 44, 48, 61, 62, 66, 71, 75, 76, 95, 99, 114, 121, 126, 143, 144, 181, 209, 238, 242, 248, 251, 255, 259, 263, 279, 282, 301, 327, 330, 340], [(8, none), (26, some 466), (33, some 564), (44, some 468), (48, some 565), (61, some 566), (62, some 567), (66, some 568), (71, some 473), (75, some 569), (76, some 570), (95, some 571), (99, some 478), (114, some 572), (121, some 479), (126, some 480), (143, some 573), (144, some 483), (181, some 574), (209, some 575), (238, some 576), (242, some 577), (248, some 578), (251, some 579), (255, some 580), (259, some 581), (263, some 61), (279, some 582), (282, some 583), (301, some 584), (327, none), (330, some 585), (340, some 586)]),
    (false, [6, 17, 43, 44, 52, 144, 181, 190, 222, 258, 293], [6, 25, 43, 44, 60, 61, 69, 71, 83, 85, 94, 110, 113, 133, 144, 190, 221, 222, 231, 247, 253, 259, 262, 315, 331, 338], [(6, none), (25, some 587), (43, none), (44, none), (60, some 588), (61, some 471), (69, some 589), (71, some 590), (83, some 591), (85, some 592), (94, some 593), (110, some 594), (113, some 595), (133, some 596), (144, none), (190, none), (221, some 597), (222, none), (231, some 598), (247, some 599), (253, some 600), (259, some 601), (262, some 602), (315, some 603), (331, some 604), (338, some 605)]),
    (false, [6, 17, 43, 44, 52, 109, 144, 181, 190, 258, 293], [6, 25, 43, 44, 60, 61, 65, 71, 83, 85, 94, 109, 110, 113, 133, 144, 190, 221, 231, 247, 253, 259, 262, 315, 331, 338], [(6, none), (25, some 607), (43, none), (44, none), (60, some 608), (61, some 609), (65, some 610), (71, some 611), (83, some 612), (85, some 613), (94, some 614), (109, none), (110, some 615), (113, some 616), (133, some 617), (144, none), (190, none), (221, some 618), (231, some 619), (247, some 620), (253, some 621), (259, some 622), (262, some 623), (315, some 624), (331, some 625), (338, some 626)]),
    (false, [6, 17, 43, 44, 52, 77, 144, 181, 222, 232, 258, 293], [6, 20, 26, 42, 43, 44, 60, 61, 66, 69, 71, 75, 83, 85, 94, 95, 99, 110, 113, 133, 143, 144, 181, 221, 222, 231, 232, 247, 253, 259, 262, 263, 315, 331, 338], [(6, none), (20, some 628), (26, some 629), (42, some 630), (43, none), (44, none), (60, some 631), (61, some 471), (66, some 472), (69, some 589), (71, some 632), (75, some 474), (83, some 591), (85, some 592), (94, some 593), (95, some 476), (99, some 633), (110, some 634), (113, some 635), (133, some 636), (143, some 482), (144, none), (181, none), (221, some 597), (222, none), (231, some 598), (232, none), (247, some 599), (253, some 600), (259, some 637), (262, some 602), (263, some 638), (315, some 603), (331, some 604), (338, some 605)]),
    (false, [6, 17, 43, 44, 52, 77, 119, 144, 181, 222, 258, 293], [5, 7, 20, 26, 41, 43, 44, 60, 61, 66, 71, 75, 83, 94, 95, 99, 121, 126, 133, 143, 144, 181, 231, 237, 238, 251, 255, 259, 262, 263, 267, 279, 282, 301, 338, 340], [(5, some 640), (7, some 641), (20, some 642), (26, some 643), (41, some 644), (43, none), (44, none), (60, some 645), (61, some 646), (66, some 647), (71, some 648), (75, some 649), (83, some 650), (94, some 651), (95, some 652), (99, some 653), (121, some 654), (126, some 655), (133, some 656), (143, some 657), (144, none), (181, none), (231, some 658), (237, some 659), (238, some 660), (251, some 661), (255, some 662), (259, some 663), (262, some 664), (263, some 665), (267, some 666), (279, some 667), (282, some 668), (301, some 669), (338, some 670), (340, some 671)]),
    (false, [6, 7, 17, 43, 44, 52, 77, 109, 144, 181, 258, 293], [5, 7, 20, 26, 41, 43, 44, 60, 61, 66, 71, 75, 83, 94, 95, 99, 121, 126, 133, 143, 144, 181, 231, 237, 238, 251, 255, 259, 262, 263, 267, 279, 282, 301, 338, 340], [(5, some 672), (7, none), (20, some 628), (26, some 629), (41, some 673), (43, none), (44, none), (60, some 631), (61, some 471), (66, some 472), (71, some 632), (75, some 474), (83, some 591), (94, some 593), (95, some 476), (99, some 633), (121, some 674), (126, some 675), (133, some 636), (143, some 482), (144, none), (181, none), (231, some 676), (237, some 677), (238, some 678), (251, some 679), (255, some 680), (259, some 681), (262, some 682), (263, some 683), (267, some 684), (279, some 685), (282, some 686), (301, some 687), (338, some 688), (340, some 689)]),
    (false, [6, 17, 43, 44, 52, 77, 109, 144, 181, 258, 292, 293], [5, 6, 24, 43, 44, 60, 61, 65, 71, 83, 85, 94, 109, 110, 113, 121, 126, 133, 144, 195, 221, 231, 238, 247, 251, 253, 255, 259, 262, 267, 279, 282, 301, 315, 331, 338, 340], [(5, some 691), (6, none), (24, some 692), (43, none), (44, none), (60, some 693), (61, some 609), (65, some 610), (71, some 694), (83, some 612), (85, some 613), (94, some 614), (109, none), (110, some 695), (113, some 696), (121, some 697), (126, some 698), (133, some 699), (144, none), (195, some 700), (221, some 701), (231, some 702), (238, some 703), (247, some 704), (251, some 705), (253, some 706), (255, some 707), (259, some 708), (262, some 709), (267, some 710), (279, some 711), (282, some 712), (301, some 713), (315, some 714), (331, some 715), (338, some 716), (340, some 717)]),
    (false, [6, 17, 43, 44, 52, 59, 68, 144, 183, 258, 293], [5, 7, 21, 26, 41, 43, 44, 53, 59, 60, 61, 66, 71, 75, 83, 87, 94, 95, 97, 99, 121, 126, 133, 141, 143, 144, 183, 231, 235, 237, 238, 251, 255, 259, 262, 263, 264, 267, 277, 279, 282, 301, 337, 338, 340], [(5, some 719), (7, some 720), (21, some 721), (26, some 722), (41, some 723), (43, none), (44, none), (53, some 724), (59, none), (60, some 725), (61, some 726), (66, some 727), (71, some 728), (75, some 729), (83, some 730), (87, some 731), (94, some 732), (95, some 733), (97, some 734), (99, some 735), (121, some 736), (126, some 737), (133, some 738), (141, some 739), (143, some 740), (144, none), (183, none), (231, some 676), (235, some 741), (237, some 677), (238, some 678), (251, some 679), (255, some 680), (259, some 488), (262, some 682), (263, some 683), (264, some 742), (267, some 684), (277, some 743), (279, some 685), (282, some 686), (301, some 687), (337, some 744), (338, some 688), (340, some 689)]),
    (false, [6, 17, 43, 44, 52, 59, 68, 70, 144, 258, 293], [1, 5, 7, 22, 26, 41, 43, 44, 53, 59, 60, 61, 66, 71, 75, 83, 87, 94, 95, 97, 99, 106, 121, 126, 131, 133, 141, 143, 144, 185, 224, 231, 235, 237, 238, 251, 255, 259, 262, 263, 264, 267, 272, 277, 279, 282, 284, 300, 301, 337, 338, 340], [(1, some 528), (5, some 745), (7, some 746), (22, some 529), (26, some 530), (41, some 531), (43, none), (44, none), (53, some 533), (59, none), (60, some 747), (61, some 535), (66, some 536), (71, some 537), (75, some 538), (83, some 748), (87, some 539), (94, some 749), (95, some 540), (97, some 541), (99, some 542), (106, some 543), (121, some 544), (126, some 545), (131, some 546), (133, some 750), (141, some 547), (143, some 548), (144, none), (185, some 751), (224, some 752), (231, some 676), (235, some 741), (237, some 677), (238, some 678), (251, some 679), (255, some 680), (259, some 753), (262, some 682), (263, some 683), (264, some 742), (267, some 684), (272, some 754), (277, some 743), (279, some 685), (282, some 686), (284, some 755), (300, some 756), (301, some 687), (337, some 744), (338, some 688), (340, some 689)]),
    (false, [6, 17, 43, 44, 52, 68, 144, 172, 232, 258, 293], [7, 21, 26, 42, 43, 44, 53, 60, 61, 63, 66, 71, 73, 75, 83, 87, 94, 95, 99, 103, 133, 141, 143, 144, 187, 231, 232, 235, 259, 262, 263, 273, 338], [(7, some 757), (21, some 721), (26, some 722), (42, some 758), (43, none), (44, none), (53, some 724), (60, some 725), (61, some 726), (63, some 759), (66, some 727), (71, some 728), (73, some 760), (75, some 729), (83, some 730), (87, some 731), (94, some 732), (95, some 733), (99, some 735), (103, some 761), (133, some 738), (141, some 739), (143, some 740), (144, none), (187, some 762), (231, some 763), (232, none), (235, some 764), (259, some 637), (262, some 765), (263, some 766), (273, some 767), (338, some 768)]),
    (false, [6, 17, 43, 44, 52, 68, 119, 144, 172, 258, 293], [5, 7, 21, 26, 41, 43, 44, 53, 60, 61, 63, 66, 71, 73, 75, 83, 87, 94, 95, 99, 103, 121, 126, 133, 141, 143, 144, 187, 231, 235, 237, 238, 251, 255, 259, 262, 263, 267, 273, 279, 282, 301, 338, 340], [(5, some 719), (7, some 757), (21, some 721), (26, some 722), (41, some 723), (43, none), (44, none), (53, some 724), (60, some 725), (61, some 726), (63, some 759), (66, some 727), (71, some 728), (73, some 760), (75, some 729), (83, some 730), (87, some 731), (94, some 732), (95, some 733), (99, some 735), (103, some 761), (121, some 736), (126, some 737), (133, some 738), (141, some 739), (143, some 740), (144, none), (187, some 769), (231, some 770), (235, some 771), (237, some 501), (238, some 772), (251, some 773), (255, some 774), (259, some 125), (262, some 775), (263, some 63), (267, some 776), (273, some 777), (279, some 778), (282, some 779), (301, some 780), (338, some 781), (340, some 782)]),
    (false, [6, 17, 52, 144, 193, 258, 293, 327, 328], [61, 71, 144, 193, 259, 327, 328], [(61, some 791), (71, some 590), (144, none), (193, none), (259, some 792), (327, none), (328, none)]),
    (false, [6, 7, 17, 44, 52, 144, 193, 258, 293, 327], [5, 7, 26, 33, 41, 44, 60, 61, 66, 71, 75, 83, 94, 95, 99, 121, 126, 133, 143, 144, 181, 231, 237, 238, 251, 255, 259, 262, 263, 267, 279, 282, 301, 327, 338, 340], [(5, some 793), (7, none), (26, some 794), (33, some 795), (41, some 796), (44, none), (60, some 797), (61, some 798), (66, some 799), (71, some 800), (75, some 801), (83, some 802), (94, some 803), (95, some 804), (99, some 805), (121, some 674), (126, some 675), (133, some 806), (143, some 807), (144, none), (181, some 808), (231, some 676), (237, some 677), (238, some 678), (251, some 679), (255, some 680), (259, some 809), (262, some 682), (263, some 683), (267, some 684), (279, some 685), (282, some 686), (301, some 687), (327, none), (338, some 688), (340, some 689)]),
    (false, [6, 17, 44, 52, 144, 191, 193, 222, 258, 292, 293, 327], [6, 37, 44, 61, 69, 71, 85, 110, 113, 144, 191, 222, 247, 253, 259, 315, 327, 331], [(6, none), (37, some 810), (44, none), (61, some 798), (69, some 811), (71, some 590), (85, some 812), (110, some 594), (113, some 595), (144, none), (191, none), (222, none), (247, some 599), (253, some 600), (259, some 813), (315, some 603), (327, none), (331, some 604)]),
    (false, [6, 17, 44, 52, 78, 144, 190, 193, 222, 258, 292, 293, 327], [6, 38, 44, 60, 61, 69, 71, 83, 85, 94, 110, 113, 133, 144, 190, 221, 222, 231, 247, 253, 259, 262, 315, 327, 331, 338], [(6, none), (38, some 823), (44, none), (60, some 824), (61, some 798), (69, some 811), (71, some 825), (83, some 802), (85, some 812), (94, some 803), (110, some 826), (113, some 827), (133, some 828), (144, none), (190, none), (221, some 597), (222, none), (231, some 598), (247, some 599), (253, some 600), (259, some 601), (262, some 602), (315, some 603), (327, none), (331, some 604), (338, some 605)]),
    (false, [6, 17, 44, 52, 78, 109, 144, 190, 193, 258, 292, 293, 327], [6, 38, 44, 60, 61, 65, 71, 83, 85, 94, 109, 110, 113, 133, 144, 190, 221, 231, 247, 253, 259, 262, 315, 327, 331, 338], [(6, none), (38, some 829), (44, none), (60, some 830), (61, some 831), (65, some 832), (71, some 833), (83, some 834), (85, some 835), (94, some 836), (109, none), (110, some 837), (113, some 838), (133, some 839), (144, none), (190, none), (221, some 840), (231, some 841), (247, some 842), (253, some 843), (259, some 844), (262, some 845), (315, some 846), (327, none), (331, some 847), (338, some 848)]),
    (false, [6, 17, 44, 52, 77, 78, 109, 144, 193, 258, 292, 293, 327], [5, 6, 36, 44, 60, 61, 65, 71, 83, 85, 94, 109, 110, 113, 121, 126, 133, 144, 195, 221, 231, 238, 247, 251, 253, 255, 259, 262, 267, 279, 282, 301, 315, 327, 331, 338, 340], [(5, some 851), (6, none), (36, some 852), (44, none), (60, some 853), (61, some 854), (65, some 855), (71, some 856), (83, some 857), (85, some 858), (94, some 859), (109, none), (110, some 860), (113, some 861), (121, some 862), (126, some 863), (133, some 864), (144, none), (195, some 865), (221, some 866), (231, some 867), (238, some 868), (247, some 869), (251, some 870), (253, some 871), (255, some 872), (259, some 873), (262, some 874), (267, some 875), (279, some 876), (282, some 877), (301, some 878), (315, some 879), (327, none), (331, some 880), (338, some 881), (340, some 882)]),
    (false, [6, 17, 52, 80, 144, 258, 293, 327], [5, 7, 26, 33, 41, 44, 60, 61, 66, 71, 75, 83, 94, 95, 99, 121, 126, 133, 143, 144, 181, 231, 237, 238, 251, 255, 259, 262, 263, 267, 279, 282, 301, 327, 338, 340], [(5, some 892), (7, some 893), (26, some 894), (33, some 895), (41, some 896), (44, some 897), (60, some 898), (61, some 899), (66, some 900), (71, some 901), (75, some 902), (83, some 903), (94, some 904), (95, some 905), (99, some 906), (121, some 907), (126, some 908), (133, some 909), (143, some 910), (144, none), (181, some 911), (231, some 912), (237, some 913), (238, some 914), (251, some 915), (255, some 916), (259, some 917), (262, some 918), (263, some 919), (267, some 920), (279, some 921), (282, some 922), (301, some 923), (327, none), (338, some 924), (340, some 925)]),
    (false, [6, 17, 52, 257, 258, 293, 327], [61, 71, 197, 257, 259, 327, 328], [(61, some 931), (71, some 932), (197, some 933), (257, none), (259, some 934), (327, none), (328, some 935)]),
    (false, [17, 43, 44, 52, 144, 258, 291, 293], [4, 23, 43, 44, 61, 67, 69, 71, 85, 88, 92, 110, 113, 115, 117, 144, 191, 199, 222, 233, 245, 247, 253, 259, 260, 315, 331], [(4, some 936), (23, some 937), (43, none), (44, none), (61, some 471), (67, some 938), (69, some 589), (71, some 939), (85, some 592), (88, some 940), (92, some 941), (110, some 594), (113, some 595), (115, some 942), (117, some 943), (144, none), (191, some 944), (199, some 945), (222, some 946), (233, some 947), (245, some 948), (247, some 949), (253, some 950), (259, some 951), (260, some 952), (315, some 953), (331, some 954)]),
    (false, [17, 43, 44, 52, 257, 258, 291, 293], [10, 23, 43, 44, 61, 69, 71, 85, 102, 110, 113, 117, 191, 199, 220, 222, 245, 247, 249, 253, 257, 259, 260, 278, 302, 315, 331, 334], [(10, some 955), (23, some 937), (43, none), (44, none), (61, some 471), (69, some 589), (71, some 956), (85, some 592), (102, some 957), (110, some 958), (113, some 595), (117, some 959), (191, some 960), (199, some 945), (220, some 961), (222, some 946), (245, some 948), (247, some 949), (249, some 962), (253, some 950), (257, none), (259, some 951), (260, some 952), (278, some 963), (302, some 964), (315, some 953), (331, some 954), (334, some 965)]),
    (false, [17, 43, 52, 197, 257, 258, 291, 293, 328], [43, 61, 71, 197, 257, 259, 328], [(43, none), (61, some 471), (71, some 966), (197, none), (257, none), (259, some 951), (328, none)]),
    (false, [17, 43, 52, 84, 257, 258, 291, 293, 328], [10, 19, 43, 61, 71, 102, 117, 211, 220, 245, 249, 257, 259, 260, 278, 302, 328, 334], [(10, some 972), (19, some 973), (43, none), (61, some 471), (71, some 974), (102, some 975), (117, some 976), (211, some 977), (220, some 961), (245, some 948), (249, some 962), (257, none), (259, some 951), (260, some 952), (278, some 963), (302, some 964), (328, none), (334, some 965)]),
    (false, [17, 52, 197, 257, 258, 291, 293, 327, 328], [61, 71, 197, 257, 259, 327, 328], [(61, some 791), (71, some 983), (197, none), (257, none), (259, some 951), (327, none), (328, none)]),
    (false, [17, 44, 52, 197, 257, 258, 291, 293, 327], [10, 30, 44, 61, 71, 102, 117, 192, 220, 245, 249, 257, 259, 260, 278, 302, 327, 334], [(10, some 992), (30, some 993), (44, none), (61, some 994), (71, some 995), (102, some 996), (117, some 997), (192, some 998), (220, some 999), (245, some 1000), (249, some 1001), (257, none), (259, some 1002), (260, some 1003), (278, some 1004), (302, some 1005), (327, none), (334, some 1006)]),
    (false, [17, 52, 144, 197, 258, 291, 293, 327, 328], [61, 71, 144, 193, 259, 327, 328], [(61, some 791), (71, some 939), (144, none), (193, some 1007), (259, some 951), (327, none), (328, none)]),
    (false, [17, 44, 52, 84, 144, 258, 291, 293, 327], [4, 37, 44, 61, 67, 69, 71, 85, 88, 92, 110, 113, 115, 117, 144, 191, 199, 222, 233, 245, 247, 253, 259, 260, 315, 327, 331], [(4, some 1012), (37, some 1013), (44, none), (61, some 1014), (67, some 1015), (69, some 1016), (71, some 1017), (85, some 1018), (88, some 1019), (92, some 1020), (110, some 1021), (113, some 1022), (115, some 1023), (117, some 1024), (144, none), (191, some 1025), (199, some 1026), (222, some 1027), (233, some 1028), (245, some 1029), (247, some 1030), (253, some 1031), (259, some 1032), (260, some 1033), (315, some 1034), (327, none), (331, some 1035)]),
    (false, [17, 44, 52, 84, 257, 258, 291, 293, 327], [10, 37, 44, 61, 69, 71, 85, 102, 110, 113, 117, 191, 199, 220, 222, 245, 247, 249, 253, 257, 259, 260, 278, 302, 315, 327, 331, 334], [(10, some 1037), (37, some 1038), (44, none), (61, some 1039), (69, some 1040), (71, some 1041), (85, some 1042), (102, some 1043), (110, some 1044), (113, some 1045), (117, some 1046), (191, some 1047), (199, some 1048), (220, some 1049), (222, some 1050), (245, some 1051), (247, some 1052), (249, some 1053), (253, some 1054), (257, none), (259, some 1055), (260, some 1056), (278, some 1057), (302, some 1058), (315, some 1059), (327, none), (331, some 1060), (334, some 1061)]),
    (false, [9, 17, 52, 84, 144, 258, 291, 293, 327, 328], [61, 71, 144, 193, 259, 327, 328], [(61, some 1062), (71, some 1063), (144, none), (193, some 1064), (259, some 1032), (327, none), (328, none)]),
    (false, [9, 17, 52, 84, 257, 258, 291, 293, 327, 328], [9, 28, 61, 67, 71, 88, 92, 115, 117, 211, 233, 245, 257, 259, 260, 327, 328], [(9, none), (28, some 1065), (61, some 1062), (67, some 1066), (71, some 1063), (88, some 1067), (92, some 1068), (115, some 1069), (117, some 1070), (211, some 1071), (233, some 1072), (245, some 1073), (257, none), (259, some 1074), (260, some 1075), (327, none), (328, none)]),
    (false, [17, 52, 84, 257, 258, 291, 293, 294, 327, 328], [10, 30, 61, 71, 102, 117, 211, 220, 245, 249, 257, 259, 260, 278, 302, 327, 328, 334], [(10, some 1076), (30, some 1077), (61, some 1062), (71, some 1078), (102, some 1079), (117, some 1080), (211, some 1081), (220, some 1082), (245, some 1083), (249, some 1084), (257, none), (259, some 1085), (260, some 1086), (278, some 1087), (302, some 1088), (327, none), (328, none), (334, some 1089)]),
    (false, [17, 52, 84, 144, 258, 291, 293, 294, 327, 328], [61, 71, 144, 193, 259, 327, 328], [(61, some 1062), (71, some 1017), (144, none), (193, some 1090), (259, some 1085), (327, none), (328, none)])
  ]


private theorem array_project_prefix {α β : Type} (xs : Array α) (f : α → β)
    (fallback : α) (n : ℕ) (keys : List β)
    (hkeys : (xs.toList.take n).map f = keys) (i : ℕ) (hi : i < n) :
    f (xs[i]?.getD fallback) = keys[i]?.getD (f fallback) := by
  calc
    f (xs[i]?.getD fallback) = (xs.toList.map f)[i]?.getD (f fallback) := by
      rw [List.getElem?_map, Array.getElem?_toList]
      exact (Option.getD_map f fallback (xs[i]?)).symm
    _ = ((xs.toList.take n).map f)[i]?.getD (f fallback) := by
      simp only [List.getElem?_map, List.getElem?_take_of_lt hi]
    _ = keys[i]?.getD (f fallback) := by rw [hkeys]

private theorem witness_row_projected (C : LateCatalog) (n : ℕ) (keys : List WKey)
    (hkeys : (C.witnesses.toList.take n).map witnessKey = keys)
    (wid : ℕ) (hi : wid - 1 < n) :
    witnessKey (lateWitnessRow C wid) = keys[wid - 1]?.getD (0, 0, 0) := by
  exact array_project_prefix C.witnesses witnessKey ⟨0, 0, 0, fun _ _ => 0⟩ n keys hkeys (wid - 1) hi

private theorem path_row_projected (C : LateCatalog) (n : ℕ) (keys : List PKey)
    (hkeys : (C.paths.toList.take n).map pathKey = keys)
    (pid : ℕ) (hi : pid - 1 < n) :
    pathKey (latePath C pid) = keys[pid - 1]?.getD (false, [], [], []) := by
  exact array_project_prefix C.paths pathKey ⟨false, [], [], [], [], [], []⟩ n keys hkeys (pid - 1) hi

private theorem witnessKeys_eq :
    (lateCatalog.witnesses.toList.take 1069).map witnessKey = witnessKeys := by
  change (((lateWitnessData1 ++ lateWitnessData2 ++ lateWitnessData3 ++
    lateWitnessData4 ++ lateWitnessData5 ++ lateWitnessData6 ++
    lateWitnessData7 ++ lateWitnessData8).toList.take 1069).map witnessKey) = witnessKeys
  simp only [Array.toList_append, List.map_take, List.map_append]
  rfl

private theorem pathKeys_eq :
    (lateCatalog.paths.toList.take 49).map pathKey = pathKeys := by
  change (((latePathData1 ++ latePathData2 ++ latePathData3 ++
    latePathData4).toList.take 49).map pathKey) = pathKeys
  simp only [Array.toList_append, List.map_take, List.map_append]
  rfl

private def lookupWitness (wid : ℕ) : Option WKey :=
  if 0 < wid ∧ wid ≤ 1069 then witnessKeys[wid - 1]? else none

private def lookupPath (pid : ℕ) : Option PKey :=
  if 0 < pid ∧ pid ≤ 49 then pathKeys[pid - 1]? else none

private theorem witnessKey_fields (r : LateWitnessRow) (k : WKey)
    (h : witnessKey r = k) :
    r.lower = k.1 ∧ r.upper = k.2.1 ∧ r.rectangle = k.2.2 := by
  exact ⟨congrArg Prod.fst h, congrArg (fun x => x.2.1) h,
    congrArg (fun x => x.2.2) h⟩

private theorem pathKey_fields (r : LatePath) (k : PKey)
    (h : pathKey r = k) :
    r.right3 = k.1 ∧ r.incoming = k.2.1 ∧
    r.required = k.2.2.1 ∧ r.implications = k.2.2.2 := by
  exact ⟨congrArg Prod.fst h, congrArg (fun x => x.2.1) h,
    congrArg (fun x => x.2.2.1) h, congrArg (fun x => x.2.2.2) h⟩

private theorem lookupWitness_faithful (wid : ℕ) (w : WKey)
    (h : lookupWitness wid = some w) :
    (lateWitnessRow lateCatalog wid).lower = w.1 ∧
    (lateWitnessRow lateCatalog wid).upper = w.2.1 ∧
    (lateWitnessRow lateCatalog wid).rectangle = w.2.2 := by
  unfold lookupWitness at h
  split at h
  next hw =>
    have hi : wid - 1 < 1069 := by omega
    have hs : witnessKeys[wid - 1]?.getD (0, 0, 0) = w :=
      congrArg (fun o : Option WKey => o.getD (0, 0, 0)) h
    have he := (witness_row_projected lateCatalog 1069 witnessKeys witnessKeys_eq wid hi).trans hs
    exact witnessKey_fields (lateWitnessRow lateCatalog wid) w he
  next => contradiction

private theorem lookupPath_faithful (pid : ℕ) (p : PKey)
    (h : lookupPath pid = some p) :
    (latePath lateCatalog pid).right3 = p.1 ∧
    (latePath lateCatalog pid).incoming = p.2.1 ∧
    (latePath lateCatalog pid).required = p.2.2.1 ∧
    (latePath lateCatalog pid).implications = p.2.2.2 := by
  unfold lookupPath at h
  split at h
  next hp =>
    have hi : pid - 1 < 49 := by omega
    have hs : pathKeys[pid - 1]?.getD (false, [], [], []) = p :=
      congrArg (fun o : Option PKey => o.getD (false, [], [], [])) h
    have he := (path_row_projected lateCatalog 49 pathKeys pathKeys_eq pid hi).trans hs
    exact pathKey_fields (latePath lateCatalog pid) p he
  next => contradiction


private theorem rectangle_list (i : ℕ) : lateRectangle lateCatalog i =
    lateRectangleData.toList[i - 1]?.getD ⟨0, 0, 0, 0⟩ := by
  change lateRectangleData[i - 1]?.getD ⟨0, 0, 0, 0⟩ = _
  rw [Array.getElem?_toList]

private def rectangleTransitions : List ((ℕ × Bool × Bool) × ℕ) :=
  [
    ((3, true, false), 2),
    ((3, true, true), 4),
    ((7, true, false), 5),
    ((7, true, true), 11),
    ((8, true, false), 7),
    ((8, true, true), 15),
    ((9, true, false), 8),
    ((9, true, true), 19),
    ((11, true, false), 10),
    ((11, true, true), 12),
    ((14, true, false), 13),
    ((14, true, true), 16),
    ((15, true, false), 14),
    ((15, true, true), 17),
    ((16, false, false), 1),
    ((16, false, true), 27),
    ((19, true, false), 18),
    ((19, true, true), 21),
    ((21, true, false), 20),
    ((21, true, true), 23),
    ((23, true, false), 22),
    ((23, true, true), 24),
    ((24, false, false), 3),
    ((24, false, true), 30),
    ((27, true, false), 26),
    ((27, true, true), 28),
    ((30, true, false), 29),
    ((30, true, true), 31),
    ((31, false, false), 25),
    ((31, false, true), 32)
  ]


private theorem rectangle_map :
    rectangleTransitions.map (fun p => lateSubrect
      (lateRectangleData.toList[p.1.1 - 1]?.getD ⟨0, 0, 0, 0⟩) p.1.2.1 p.1.2.2) =
    rectangleTransitions.map (fun p =>
      lateRectangleData.toList[p.2 - 1]?.getD ⟨0, 0, 0, 0⟩) := by
  norm_num [rectangleTransitions, lateRectangleData, lateSubrect]

private def lookupRectangle (rid : ℕ) (axis right : Bool) : Option ℕ :=
  rectangleTransitions.lookup (rid, axis, right)

private theorem lookupRectangle_faithful (rid : ℕ) (axis right : Bool) (child : ℕ)
    (h : lookupRectangle rid axis right = some child) :
    lateSubrect (lateRectangle lateCatalog rid) axis right = lateRectangle lateCatalog child := by
  have hm : ((rid, axis, right), child) ∈ rectangleTransitions := by
    rcases List.lookup_eq_some_iff.mp h with ⟨before, after, he, _⟩
    rw [he]
    simp
  have he := List.map_inj_left.mp rectangle_map ((rid, axis, right), child) hm
  rw [rectangle_list rid, rectangle_list child]
  exact he


private def decodeWitness (w : WKey) : WitnessKey := ⟨w.1, w.2.1, w.2.2⟩

private def decodePath (p : PKey) : PathKey := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩

private def otherMetadata : IndexMetadata where
  boundCount := 341
  proofCount := 1494
  witnessCount := 1473
  pathCount := 63
  complement := lookupComplement
  proofNode := lookupProof
  witnessKey := fun wid => (lookupWitness wid).map decodeWitness
  pathKey := fun pid => (lookupPath pid).map decodePath
  rectChild := lookupRectangle

private theorem other_faithful : MetadataFaithful lateCatalog otherMetadata := by
  refine {
    bound_count := ?_
    proof_count := ?_
    witness_count := ?_
    path_count := ?_
    complement := ?_
    proof_node := ?_
    witness_key := ?_
    path_key := ?_
    rect_child := ?_
  }
  · change 341 = lateBoundData.size
    rfl
  · change 1494 = lateProofData.size
    rfl
  · change 1473 = (lateWitnessData1 ++ lateWitnessData2 ++ lateWitnessData3 ++
      lateWitnessData4 ++ lateWitnessData5 ++ lateWitnessData6 ++
      lateWitnessData7 ++ lateWitnessData8).size
    simp only [Array.size_append]
    rfl
  · change 63 = (latePathData1 ++ latePathData2 ++ latePathData3 ++ latePathData4).size
    simp only [Array.size_append]
    rfl
  · intro i j h
    exact lookupComplement_faithful i j h
  · intro pid node h
    exact lookupProof_faithful pid node h
  · intro wid w h
    change (lookupWitness wid).map decodeWitness = some w at h
    rcases Option.map_eq_some_iff.mp h with ⟨key, hlookup, he⟩
    cases he
    exact lookupWitness_faithful wid key hlookup
  · intro pid p h
    change (lookupPath pid).map decodePath = some p at h
    rcases Option.map_eq_some_iff.mp h with ⟨key, hlookup, he⟩
    cases he
    exact lookupPath_faithful pid key hlookup
  · intro rid axis right child h
    exact lookupRectangle_faithful rid axis right child h

private theorem other_root_rectangle : lateRectangle lateCatalog 9 = lateRootRectangle false := by rfl



private def proofBlocks : List (List LateProofNode) :=
  [
    [.pair 1, .pair 2, .pair 3, .pair 4, .pair 5, .pair 6, .pair 7, .pair 8, .pair 9, .pair 10, .pair 11, .pair 12, .pair 13, .pair 14, .pair 15, .pair 16, .pair 17, .pair 18, .pair 19, .pair 20, .pair 21, .pair 22, .pair 23, .pair 24, .pair 25, .pair 26, .pair 27, .pair 28, .pair 29, .pair 30, .pair 31, .pair 32],
    [.pair 33, .pair 34, .pair 35, .pair 36, .pair 37, .pair 38, .pair 39, .pair 40, .pair 41, .pair 42, .pair 43, .pair 44, .pair 45, .pair 46, .pair 47, .pair 48, .pair 49, .split true 51 52, .pair 50, .split true 53 54, .pair 51, .split true 55 56, .pair 52, .pair 53, .pair 54, .pair 55, .pair 56, .pair 57, .pair 58, .pair 59, .pair 60, .pair 61],
    [.pair 62, .pair 63, .pair 64, .pair 65, .pair 66, .pair 67, .pair 68, .pair 69, .pair 70, .pair 71, .pair 72, .pair 73, .pair 74, .pair 75, .pair 76, .pair 77, .pair 78, .pair 79, .pair 80, .pair 81, .pair 82, .pair 83, .pair 84, .pair 85, .pair 86, .pair 87, .pair 88, .pair 89, .pair 90, .pair 91, .pair 92, .pair 93],
    [.pair 94, .pair 95, .pair 96, .pair 97, .pair 98, .pair 99, .pair 100, .pair 101, .pair 102, .pair 103, .pair 104, .pair 105, .pair 106, .pair 107, .pair 108, .pair 109, .pair 110, .pair 111, .pair 112, .pair 113, .pair 114, .pair 115, .pair 116, .pair 117, .pair 118, .pair 119, .pair 120, .pair 121, .pair 122, .pair 123, .pair 124, .pair 125],
    [.pair 126, .pair 127, .pair 128, .pair 129, .pair 130, .pair 131, .pair 132, .pair 133, .pair 134, .pair 135, .pair 136, .pair 137, .pair 138, .pair 139, .pair 140, .pair 141, .pair 142, .pair 143, .pair 144, .pair 145, .pair 146, .pair 147, .pair 148, .pair 149, .pair 150, .pair 151, .pair 152, .pair 153, .pair 154, .pair 155, .pair 156, .pair 157],
    [.pair 158, .pair 159, .pair 160, .pair 161, .pair 162, .pair 163, .pair 164, .pair 165, .pair 166, .pair 167, .pair 168, .pair 169, .pair 170, .pair 171, .pair 172, .pair 173, .pair 174, .pair 175, .pair 176, .pair 177, .pair 178, .pair 179, .pair 180, .pair 181, .pair 182, .pair 183, .pair 184, .pair 185, .pair 186, .pair 187, .pair 188, .pair 189],
    [.pair 190, .pair 191, .pair 192, .pair 193, .pair 194, .pair 195, .pair 196, .pair 197, .pair 198, .pair 199, .pair 200, .pair 201, .pair 202, .pair 203, .pair 204, .pair 205, .pair 206, .pair 207, .pair 208, .pair 209, .pair 210, .pair 211, .pair 212, .pair 213, .pair 214, .pair 215, .pair 216, .pair 217, .pair 218, .pair 219, .pair 220, .pair 221],
    [.pair 222, .pair 223, .pair 224, .pair 225, .pair 226, .pair 227, .pair 228, .pair 229, .pair 230, .pair 231, .pair 232, .pair 233, .pair 234, .pair 235, .pair 236, .pair 237, .pair 238, .pair 239, .pair 240, .pair 241, .pair 242, .pair 243, .pair 244, .pair 245, .pair 246, .pair 247, .pair 248, .pair 249, .pair 250, .pair 251, .pair 252, .pair 253],
    [.pair 254, .pair 255, .pair 256, .pair 257, .pair 258, .pair 259, .pair 260, .pair 261, .pair 262, .pair 263, .pair 264, .pair 265, .pair 266, .pair 267, .pair 268, .pair 269, .pair 270, .pair 271, .pair 272, .pair 273, .pair 274, .pair 275, .pair 276, .pair 277, .pair 278, .pair 279, .pair 280, .pair 281, .pair 282, .pair 283, .pair 284, .pair 285],
    [.pair 286, .pair 287, .pair 288, .pair 289, .pair 290, .pair 291, .pair 292, .pair 293, .pair 294, .pair 295, .pair 296, .pair 297, .pair 298, .pair 299, .pair 300, .pair 301, .pair 302, .pair 303, .pair 304, .pair 305, .pair 306, .pair 307, .pair 308, .pair 309, .pair 310, .pair 311, .pair 312, .pair 313, .pair 314, .pair 315, .pair 316, .pair 317],
    [.pair 318, .pair 319, .pair 320, .pair 321, .pair 322, .pair 323, .pair 324, .pair 325, .pair 326, .pair 327, .pair 328, .pair 329, .pair 330, .pair 331, .pair 332, .pair 333, .pair 334, .pair 335, .pair 336, .pair 337, .pair 338, .pair 339, .pair 340, .pair 341, .pair 342, .pair 343, .pair 344, .pair 345, .pair 346, .pair 347, .pair 348, .pair 349],
    [.pair 350, .pair 351, .pair 352, .pair 353, .pair 354, .pair 355, .pair 356, .pair 357, .pair 358, .pair 359, .pair 360, .pair 361, .pair 362, .pair 363, .pair 364, .pair 365, .pair 366, .pair 367, .pair 368, .pair 369, .pair 370, .pair 371, .pair 372, .pair 373, .pair 374, .pair 375, .pair 376, .pair 377, .pair 378, .pair 379, .pair 380, .pair 381],
    [.pair 382, .pair 383, .pair 384, .pair 385, .pair 386, .pair 387, .pair 388, .pair 389, .pair 390, .pair 391, .pair 392, .pair 393, .pair 394, .pair 395, .pair 396, .pair 397, .pair 398, .pair 399, .pair 400, .pair 401, .pair 402, .pair 403, .pair 404, .pair 405, .pair 406, .pair 407, .pair 408, .pair 409, .pair 410, .pair 411, .pair 412, .pair 413],
    [.pair 414, .pair 415, .pair 416, .pair 417, .pair 418, .pair 419, .pair 420, .pair 421, .pair 422, .pair 423, .pair 424, .pair 425, .pair 426, .pair 427, .pair 428, .pair 429, .pair 430, .pair 431, .pair 432, .pair 433, .pair 434, .pair 435, .pair 436, .pair 437, .pair 438, .pair 439, .pair 440, .pair 441, .pair 442, .pair 443, .pair 444, .pair 445],
    [.pair 446, .pair 447, .pair 448, .pair 449, .pair 450, .pair 451, .pair 452, .pair 453, .pair 454, .pair 455, .pair 456, .pair 457, .pair 458, .pair 459, .pair 460, .pair 461, .pair 462, .pair 463, .pair 464, .pair 465, .pair 466, .pair 467, .pair 468, .pair 469, .pair 470, .pair 471, .pair 472, .pair 473, .pair 474, .pair 475, .pair 476, .pair 477],
    [.pair 478, .pair 479, .pair 480, .pair 481, .pair 482, .pair 483, .pair 484, .pair 485, .pair 486, .pair 487, .pair 488, .pair 489, .pair 490, .pair 491, .pair 492, .pair 493, .pair 494, .pair 495, .pair 496, .pair 497, .pair 498, .pair 499, .pair 500, .pair 501, .pair 502, .pair 503, .pair 504, .pair 505, .pair 506, .pair 507, .pair 508, .pair 509],
    [.pair 510, .pair 511, .pair 512, .pair 513, .pair 514, .pair 515, .pair 516, .pair 517, .pair 518, .pair 519, .pair 520, .pair 521, .pair 522, .pair 523, .pair 524, .pair 525, .pair 526, .pair 527, .pair 528, .pair 529, .pair 530, .pair 531, .pair 532, .pair 533, .pair 534, .pair 535, .pair 536, .pair 537, .pair 538, .pair 539, .pair 540, .pair 541],
    [.pair 542, .pair 543, .pair 544, .pair 545, .pair 546, .pair 547, .pair 548, .pair 549, .pair 550, .pair 551, .pair 552, .pair 553, .pair 554, .pair 555, .pair 556, .pair 557, .pair 558, .pair 559, .pair 560, .pair 561, .pair 562, .pair 563, .pair 564, .pair 565, .pair 566, .pair 567, .pair 568, .pair 569, .pair 570, .pair 571, .pair 572, .pair 573],
    [.pair 574, .pair 575, .pair 576, .pair 577, .pair 578, .pair 579, .pair 580, .pair 581, .pair 582, .pair 583, .pair 584, .pair 585, .pair 586, .pair 587, .pair 588, .pair 589, .pair 590, .pair 591, .pair 592, .pair 593, .pair 594, .pair 595, .pair 596, .pair 597, .pair 598, .pair 599, .pair 600, .pair 601, .pair 602, .pair 603, .pair 604, .pair 605],
    [.pair 606, .pair 607, .pair 608, .pair 609, .pair 610, .pair 611, .pair 612, .pair 613, .pair 614, .pair 615, .pair 616, .pair 617, .pair 618, .pair 619, .pair 620, .pair 621, .pair 622, .pair 623, .pair 624, .pair 625, .pair 626, .pair 627, .pair 628, .pair 629, .pair 630, .pair 631, .pair 632, .pair 633, .pair 634, .pair 635, .pair 636, .pair 637],
    [.pair 638, .pair 639, .pair 640, .pair 641, .pair 642, .pair 643, .pair 644, .pair 645, .pair 646, .pair 647, .pair 648, .pair 649, .pair 650, .pair 651, .pair 652, .pair 653, .pair 654, .pair 655, .pair 656, .pair 657, .pair 658, .pair 659, .pair 660, .pair 661, .pair 662, .pair 663, .pair 664, .pair 665, .pair 666, .pair 667, .pair 668, .pair 669],
    [.pair 670, .pair 671, .pair 672, .pair 673, .pair 674, .pair 675, .pair 676, .pair 677, .pair 678, .pair 679, .pair 680, .pair 681, .pair 682, .pair 683, .pair 684, .pair 685, .pair 686, .pair 687, .pair 688, .pair 689, .pair 690, .pair 691, .pair 692, .pair 693, .pair 694, .pair 695, .pair 696, .pair 697, .pair 698, .pair 699, .pair 700, .pair 701],
    [.pair 702, .pair 703, .pair 704, .pair 705, .pair 706, .pair 707, .pair 708, .pair 709, .pair 710, .pair 711, .pair 712, .pair 713, .pair 714, .pair 715, .pair 716, .pair 717, .pair 718, .pair 719, .pair 720, .pair 721, .pair 722, .pair 723, .pair 724, .pair 725, .pair 726, .pair 727, .pair 728, .pair 729, .pair 730, .pair 731, .pair 732, .pair 733],
    [.pair 734, .pair 735, .pair 736, .pair 737, .pair 738, .pair 739, .pair 740, .pair 741, .pair 742, .pair 743, .pair 744, .pair 745, .pair 746, .pair 747, .pair 748, .pair 749, .pair 750, .pair 751, .pair 752, .pair 753, .pair 754, .pair 755, .pair 756, .pair 757, .pair 758, .pair 759, .pair 760, .pair 761, .pair 762, .pair 763, .pair 764, .pair 765],
    [.pair 766, .pair 767, .pair 768, .pair 769, .pair 770, .pair 771, .pair 772, .pair 773, .pair 774, .pair 775, .pair 776, .pair 777, .pair 778, .pair 779, .split true 784 785, .pair 780, .pair 781, .split true 787 788, .pair 782, .split true 789 790, .pair 783, .pair 784, .pair 785, .pair 786, .pair 787, .pair 788, .pair 789, .pair 790, .pair 791, .pair 792, .pair 793, .pair 794],
    [.pair 795, .pair 796, .pair 797, .pair 798, .pair 799, .pair 800, .pair 801, .pair 802, .pair 803, .pair 804, .pair 805, .pair 806, .pair 807, .split true 815 822, .split true 816 821, .split true 817 818, .pair 808, .split true 819 820, .pair 809, .pair 810, .pair 811, .pair 812, .pair 813, .pair 814, .pair 815, .pair 816, .pair 817, .pair 818, .pair 819, .pair 820, .pair 821, .pair 822],
    [.pair 823, .pair 824, .pair 825, .pair 826, .pair 827, .pair 828, .pair 829, .pair 830, .pair 831, .pair 832, .pair 833, .pair 834, .pair 835, .pair 836, .pair 837, .pair 838, .pair 839, .pair 840, .pair 841, .pair 842, .pair 843, .pair 844, .pair 845, .pair 846, .pair 847, .pair 848, .pair 849, .pair 850, .pair 851, .pair 852, .pair 853, .pair 854],
    [.pair 855, .pair 856, .pair 857, .pair 858, .pair 859, .pair 860, .pair 861, .pair 862, .pair 863, .pair 864, .pair 865, .pair 866, .pair 867, .pair 868, .pair 869, .pair 870, .pair 871, .pair 872, .split true 884 885, .pair 873, .split false 886 887, .pair 874, .split true 888 889, .pair 875, .pair 876, .pair 877, .pair 878, .pair 879, .pair 880, .pair 881, .pair 882, .pair 883],
    [.pair 884, .pair 885, .pair 886, .pair 887, .pair 888, .pair 889, .pair 890, .pair 891, .pair 892, .pair 893, .pair 894, .pair 895, .pair 896, .pair 897, .pair 898, .pair 899, .pair 900, .pair 901, .pair 902, .pair 903, .pair 904, .pair 905, .pair 906, .pair 907, .pair 908, .pair 909, .pair 910, .pair 911, .pair 912, .pair 913, .pair 914, .pair 915],
    [.pair 916, .pair 917, .pair 918, .pair 919, .pair 920, .pair 921, .pair 922, .pair 923, .pair 924, .pair 925, .pair 926, .pair 927, .pair 928, .pair 929, .pair 930, .pair 931, .pair 932, .pair 933, .pair 934, .pair 935, .pair 936, .pair 937, .pair 938, .pair 939, .pair 940, .pair 941, .pair 942, .pair 943, .pair 944, .pair 945, .pair 946, .pair 947],
    [.pair 948, .pair 949, .pair 950, .pair 951, .pair 952, .pair 953, .split true 968 969, .pair 954, .split true 970 971, .pair 955, .pair 956, .pair 957, .pair 958, .pair 959, .pair 960, .pair 961, .pair 962, .split true 968 979, .split true 789 980, .split true 981 982, .pair 963, .pair 964, .pair 965, .pair 966, .pair 967, .pair 968, .pair 969, .split true 989 990, .pair 970, .pair 971, .pair 972, .pair 973],
    [.pair 974, .pair 975, .pair 976, .pair 977, .pair 978, .pair 979, .pair 980, .pair 981, .pair 982, .pair 983, .pair 984, .pair 985, .pair 986, .pair 987, .pair 988, .split true 1009 1010, .pair 989, .split true 985 971, .pair 990, .pair 991, .pair 992, .pair 993, .pair 994, .pair 995, .pair 996, .pair 997, .pair 998, .pair 999, .pair 1000, .pair 1001, .pair 1002, .pair 1003],
    [.pair 1004, .pair 1005, .pair 1006, .pair 1007, .pair 1008, .pair 1009, .pair 1010, .pair 1011, .pair 1012, .pair 1013, .pair 1014, .pair 1015, .pair 1016, .pair 1017, .pair 1018, .pair 1019, .pair 1020, .pair 1021, .pair 1022, .pair 1023, .pair 1024, .pair 1025, .pair 1026, .pair 1027, .pair 1028, .pair 1029, .pair 1030, .pair 1031, .pair 1032, .pair 1033, .pair 1034, .pair 1035],
    [.pair 1036, .pair 1037, .pair 1038, .pair 1039, .pair 1040, .pair 1041, .pair 1042, .pair 1043, .pair 1044, .pair 1045, .pair 1046, .pair 1047, .pair 1048, .pair 1049, .pair 1050, .pair 1051, .pair 1052, .pair 1053, .pair 1054, .pair 1055, .pair 1056, .pair 1057, .pair 1058, .pair 1059, .pair 1060, .pair 1061, .pair 1062, .pair 1063, .pair 1064, .pair 1065, .pair 1066, .pair 1067],
    [.pair 1068, .pair 1069]
  ]

private def witnessBlocks : List (List WKey) :=
  [
    [(12, 286, 9), (12, 287, 9), (12, 298, 9), (12, 324, 9), (12, 327, 9), (12, 328, 9), (12, 172, 9), (12, 174, 9), (12, 177, 9), (12, 184, 9), (12, 200, 9), (12, 204, 9), (12, 210, 9), (12, 217, 9), (12, 218, 9), (12, 219, 9), (12, 225, 9), (12, 229, 9), (12, 236, 9), (12, 240, 9), (12, 244, 9), (12, 254, 9), (12, 257, 9), (12, 265, 9), (90, 258, 9), (100, 258, 9), (111, 258, 9), (122, 258, 9), (130, 258, 9), (147, 258, 9), (150, 258, 9), (152, 258, 9)],
    [(154, 258, 9), (157, 258, 9), (158, 258, 9), (160, 258, 9), (161, 258, 9), (167, 258, 9), (169, 258, 9), (170, 258, 9), (15, 258, 9), (29, 258, 9), (32, 258, 9), (45, 258, 9), (49, 258, 9), (51, 258, 9), (54, 258, 9), (56, 258, 9), (58, 258, 9), (145, 258, 8), (145, 258, 18), (145, 258, 20), (12, 258, 23), (149, 286, 9), (149, 288, 9), (149, 298, 9), (149, 311, 9), (149, 327, 9), (149, 328, 9), (149, 172, 9), (149, 174, 9), (149, 184, 9), (149, 200, 9), (149, 210, 9)],
    [(149, 219, 9), (149, 240, 9), (149, 244, 9), (149, 254, 9), (149, 257, 9), (111, 297, 9), (122, 297, 9), (130, 297, 9), (139, 297, 9), (145, 194, 9), (150, 297, 9), (152, 297, 9), (157, 297, 9), (158, 297, 9), (161, 297, 9), (163, 297, 9), (166, 297, 9), (169, 297, 9), (170, 297, 9), (171, 297, 9), (15, 297, 9), (29, 297, 9), (39, 297, 9), (54, 297, 9), (56, 297, 9), (81, 286, 9), (81, 287, 9), (81, 288, 9), (81, 298, 9), (81, 319, 9), (81, 327, 9), (81, 328, 9)],
    [(81, 172, 9), (81, 174, 9), (81, 177, 9), (81, 184, 9), (81, 200, 9), (81, 204, 9), (81, 210, 9), (81, 217, 9), (81, 218, 9), (81, 219, 9), (81, 225, 9), (81, 229, 9), (81, 240, 9), (81, 244, 9), (81, 254, 9), (81, 257, 9), (149, 265, 9), (145, 202, 9), (147, 297, 9), (160, 297, 9), (145, 286, 9), (145, 287, 9), (145, 288, 9), (145, 298, 9), (145, 318, 9), (145, 172, 9), (145, 174, 9), (145, 177, 9), (145, 184, 9), (145, 200, 9), (145, 204, 9), (145, 210, 9)],
    [(145, 217, 9), (145, 218, 9), (145, 219, 9), (145, 225, 9), (145, 229, 9), (145, 236, 9), (145, 240, 9), (145, 244, 9), (145, 254, 9), (145, 257, 9), (145, 265, 9), (90, 297, 9), (128, 297, 9), (154, 297, 9), (155, 297, 9), (156, 297, 9), (167, 297, 9), (32, 297, 9), (45, 297, 9), (49, 297, 9), (51, 297, 9), (58, 297, 9), (89, 286, 9), (89, 287, 9), (89, 288, 9), (89, 298, 9), (89, 324, 9), (89, 327, 9), (89, 328, 9), (89, 172, 9), (89, 174, 9), (89, 177, 9)],
    [(89, 184, 9), (89, 200, 9), (89, 204, 9), (89, 210, 9), (89, 217, 9), (89, 218, 9), (89, 219, 9), (89, 225, 9), (89, 229, 9), (89, 236, 9), (89, 240, 9), (89, 244, 9), (89, 254, 9), (89, 257, 9), (100, 297, 9), (14, 286, 9), (14, 287, 9), (14, 298, 9), (14, 310, 9), (14, 319, 9), (14, 327, 9), (14, 328, 9), (14, 336, 9), (14, 172, 9), (14, 174, 9), (14, 177, 9), (14, 179, 9), (14, 184, 9), (14, 188, 9), (14, 200, 9), (14, 204, 9), (14, 208, 9)],
    [(14, 210, 9), (14, 212, 9), (14, 217, 9), (14, 218, 9), (14, 219, 9), (14, 225, 9), (14, 229, 9), (14, 240, 9), (14, 244, 9), (14, 254, 9), (14, 256, 9), (14, 257, 9), (111, 265, 9), (122, 265, 9), (130, 265, 9), (145, 206, 9), (147, 265, 9), (150, 265, 9), (152, 265, 9), (157, 265, 9), (158, 265, 9), (161, 265, 9), (162, 265, 9), (163, 265, 9), (169, 265, 9), (170, 265, 9), (15, 265, 9), (29, 265, 9), (54, 265, 9), (56, 265, 9), (151, 286, 9), (151, 298, 9)],
    [(151, 310, 9), (151, 311, 9), (151, 327, 9), (151, 328, 9), (151, 336, 9), (151, 172, 9), (151, 174, 9), (151, 179, 9), (151, 184, 9), (151, 188, 9), (151, 200, 9), (151, 208, 9), (151, 210, 9), (151, 212, 9), (151, 219, 9), (151, 240, 9), (151, 244, 9), (151, 254, 9), (151, 256, 9), (151, 257, 9), (111, 263, 9), (122, 263, 9), (130, 263, 9), (150, 263, 9), (152, 263, 9), (157, 263, 9), (158, 263, 9), (161, 263, 9), (163, 263, 9), (169, 263, 9), (170, 263, 9), (15, 263, 9)],
    [(29, 263, 9), (54, 263, 9), (56, 263, 9), (81, 310, 9), (81, 336, 9), (81, 179, 9), (81, 188, 9), (81, 208, 9), (81, 212, 9), (81, 256, 9), (89, 206, 9), (147, 263, 9), (160, 263, 9), (93, 286, 9), (93, 287, 9), (93, 298, 9), (93, 310, 9), (93, 324, 9), (93, 327, 9), (93, 328, 9), (93, 336, 9), (93, 172, 9), (93, 174, 9), (93, 177, 9), (93, 179, 9), (93, 184, 9), (93, 188, 9), (93, 200, 9), (93, 204, 9), (93, 208, 9), (93, 210, 9), (93, 212, 9)],
    [(93, 217, 9), (93, 218, 9), (93, 219, 9), (93, 225, 9), (93, 229, 9), (93, 236, 9), (93, 240, 9), (93, 244, 9), (93, 254, 9), (93, 256, 9), (93, 257, 9), (90, 263, 9), (100, 263, 9), (154, 263, 9), (167, 263, 9), (32, 263, 9), (45, 263, 9), (49, 263, 9), (51, 263, 9), (58, 263, 9), (145, 263, 8), (145, 263, 18), (145, 263, 20), (145, 263, 22), (145, 263, 3), (145, 263, 29), (145, 263, 25), (145, 286, 32), (145, 287, 32), (145, 298, 32), (145, 310, 32), (145, 318, 32)],
    [(145, 336, 32), (145, 172, 32), (145, 174, 32), (145, 177, 32), (145, 179, 32), (145, 184, 32), (145, 188, 32), (145, 200, 32), (145, 204, 32), (145, 208, 32), (145, 210, 32), (145, 212, 32), (145, 217, 32), (145, 218, 32), (145, 219, 32), (145, 225, 32), (145, 229, 32), (145, 236, 32), (145, 240, 32), (145, 244, 32), (145, 254, 32), (145, 256, 32), (145, 257, 32), (90, 263, 32), (111, 263, 32), (122, 263, 32), (128, 263, 32), (130, 263, 32), (147, 263, 32), (150, 263, 32), (152, 263, 32), (154, 263, 32)],
    [(155, 263, 32), (156, 263, 32), (157, 263, 32), (158, 263, 32), (160, 263, 32), (161, 263, 32), (163, 263, 32), (167, 263, 32), (169, 263, 32), (170, 263, 32), (15, 263, 32), (29, 263, 32), (32, 263, 32), (45, 263, 32), (49, 263, 32), (51, 263, 32), (54, 263, 32), (56, 263, 32), (58, 263, 32), (100, 265, 9), (101, 265, 9), (154, 265, 9), (167, 265, 9), (32, 265, 9), (45, 265, 9), (49, 265, 9), (51, 265, 9), (58, 265, 9), (137, 286, 9), (137, 298, 9), (137, 310, 9), (137, 311, 9)],
    [(11, 327, 9), (11, 328, 9), (137, 336, 9), (137, 172, 9), (137, 174, 9), (137, 175, 9), (137, 179, 9), (137, 184, 9), (137, 188, 9), (137, 189, 9), (137, 200, 9), (137, 208, 9), (137, 210, 9), (137, 212, 9), (137, 219, 9), (137, 227, 9), (137, 240, 9), (137, 244, 9), (137, 254, 9), (137, 256, 9), (137, 257, 9), (81, 299, 9), (96, 299, 9), (111, 299, 9), (122, 299, 9), (130, 299, 9), (135, 299, 9), (145, 299, 9), (149, 299, 9), (150, 299, 9), (152, 299, 9), (157, 299, 9)],
    [(158, 299, 9), (161, 299, 9), (163, 299, 9), (169, 299, 9), (170, 299, 9), (15, 299, 9), (29, 299, 9), (46, 299, 9), (54, 299, 9), (56, 299, 9), (11, 286, 9), (11, 306, 9), (11, 310, 9), (11, 336, 9), (11, 172, 9), (11, 174, 9), (11, 175, 9), (11, 179, 9), (11, 184, 9), (11, 188, 9), (11, 189, 9), (11, 200, 9), (11, 208, 9), (11, 210, 9), (11, 212, 9), (11, 219, 9), (11, 227, 9), (11, 244, 9), (11, 254, 9), (11, 256, 9), (11, 257, 9), (72, 250, 9)],
    [(96, 250, 9), (111, 250, 9), (122, 250, 9), (135, 250, 9), (145, 250, 9), (149, 250, 9), (150, 250, 9), (158, 250, 9), (163, 250, 9), (170, 250, 9), (15, 250, 9), (46, 250, 9), (54, 250, 9), (43, 305, 9), (8, 310, 9), (8, 325, 9), (8, 328, 9), (8, 336, 9), (8, 172, 9), (43, 174, 9), (43, 179, 9), (8, 184, 9), (43, 188, 9), (43, 200, 9), (43, 208, 9), (8, 210, 9), (8, 212, 9), (8, 234, 9), (8, 239, 9), (8, 254, 9), (43, 256, 9), (8, 257, 9)],
    [(122, 237, 9), (125, 237, 9), (138, 237, 9), (142, 237, 9), (145, 183, 9), (149, 237, 9), (150, 237, 9), (163, 237, 9), (165, 237, 9), (168, 237, 9), (16, 237, 9), (54, 237, 9), (57, 237, 9), (124, 310, 9), (124, 328, 9), (124, 332, 9), (124, 336, 9), (124, 172, 9), (43, 175, 9), (124, 184, 9), (43, 189, 9), (124, 210, 9), (124, 212, 9), (124, 227, 9), (124, 234, 9), (124, 239, 9), (124, 254, 9), (124, 257, 9), (96, 296, 9), (122, 296, 9), (125, 296, 9), (129, 296, 9)],
    [(135, 296, 9), (138, 296, 9), (142, 296, 9), (149, 296, 9), (150, 296, 9), (163, 296, 9), (165, 296, 9), (168, 296, 9), (16, 296, 9), (46, 296, 9), (54, 296, 9), (57, 296, 9), (70, 286, 9), (70, 306, 9), (70, 310, 9), (70, 325, 9), (70, 328, 9), (70, 336, 9), (70, 172, 9), (70, 174, 9), (70, 179, 9), (70, 184, 9), (70, 188, 9), (70, 200, 9), (70, 208, 9), (70, 210, 9), (70, 212, 9), (70, 219, 9), (70, 234, 9), (70, 239, 9), (70, 244, 9), (70, 254, 9)],
    [(70, 256, 9), (70, 257, 9), (72, 296, 9), (111, 237, 9), (145, 296, 9), (158, 237, 9), (170, 237, 9), (15, 237, 9), (70, 332, 9), (70, 175, 9), (70, 189, 9), (70, 227, 9), (111, 296, 9), (158, 296, 9), (170, 296, 9), (15, 296, 9), (8, 317, 9), (8, 332, 9), (8, 174, 9), (8, 175, 9), (8, 179, 9), (8, 188, 9), (8, 189, 9), (8, 208, 9), (8, 227, 9), (8, 256, 9), (68, 327, 9), (96, 327, 9), (125, 327, 9), (129, 327, 9), (135, 327, 9), (138, 327, 9)],
    [(142, 327, 9), (145, 327, 9), (165, 327, 9), (168, 327, 9), (16, 327, 9), (46, 327, 9), (57, 327, 9), (43, 309, 9), (6, 173, 9), (43, 182, 9), (6, 184, 9), (43, 196, 9), (43, 198, 9), (43, 207, 9), (144, 223, 9), (44, 226, 9), (44, 246, 9), (108, 222, 9), (118, 222, 9), (134, 222, 9), (140, 222, 9), (145, 190, 9), (148, 222, 9), (31, 222, 9), (47, 222, 9), (55, 222, 9), (43, 190, 7), (43, 309, 15), (109, 173, 15), (43, 174, 15), (43, 178, 15), (109, 184, 15)],
    [(43, 196, 15), (43, 198, 15), (43, 207, 15), (109, 223, 15), (43, 226, 15), (43, 246, 15), (108, 190, 15), (118, 190, 15), (134, 190, 15), (140, 190, 15), (145, 190, 15), (148, 190, 15), (31, 190, 15), (47, 190, 15), (55, 190, 15), (109, 190, 19), (43, 304, 9), (77, 310, 9), (43, 326, 9), (77, 173, 9), (77, 184, 9), (43, 212, 9), (77, 223, 9), (77, 226, 9), (77, 246, 9), (145, 232, 9), (149, 222, 9), (119, 222, 8), (119, 290, 19), (119, 292, 19), (119, 304, 19), (119, 310, 19)],
    [(119, 325, 19), (119, 173, 19), (119, 174, 19), (119, 179, 19), (119, 184, 19), (119, 188, 19), (119, 196, 19), (119, 207, 19), (119, 208, 19), (119, 212, 19), (119, 234, 19), (119, 239, 19), (119, 246, 19), (119, 256, 19), (118, 222, 19), (124, 222, 19), (125, 222, 19), (138, 222, 19), (142, 222, 19), (145, 181, 19), (148, 222, 19), (149, 222, 19), (153, 222, 19), (165, 222, 19), (168, 222, 19), (16, 222, 19), (55, 222, 19), (57, 222, 19), (43, 290, 9), (77, 325, 9), (7, 234, 9), (7, 239, 9)],
    [(118, 293, 9), (124, 293, 9), (125, 293, 9), (138, 293, 9), (142, 293, 9), (145, 181, 9), (148, 293, 9), (149, 293, 9), (153, 293, 9), (165, 293, 9), (168, 293, 9), (16, 293, 9), (55, 293, 9), (57, 293, 9), (43, 292, 7), (43, 290, 15), (43, 308, 15), (77, 173, 15), (77, 184, 15), (77, 223, 15), (77, 226, 15), (77, 234, 15), (77, 239, 15), (77, 246, 15), (82, 292, 15), (108, 292, 15), (118, 292, 15), (125, 292, 15), (134, 292, 15), (138, 292, 15), (140, 292, 15), (142, 292, 15)],
    [(145, 292, 15), (148, 292, 15), (153, 292, 15), (165, 292, 15), (168, 292, 15), (16, 292, 15), (31, 292, 15), (47, 292, 15), (55, 292, 15), (57, 292, 15), (109, 292, 19), (68, 290, 9), (59, 292, 9), (68, 305, 9), (68, 310, 9), (68, 325, 9), (68, 336, 9), (68, 173, 9), (68, 174, 9), (68, 179, 9), (68, 184, 9), (68, 188, 9), (68, 196, 9), (68, 200, 9), (68, 207, 9), (68, 208, 9), (68, 210, 9), (68, 212, 9), (68, 234, 9), (68, 239, 9), (68, 246, 9), (68, 254, 9)],
    [(68, 256, 9), (122, 293, 9), (150, 293, 9), (163, 293, 9), (54, 293, 9), (70, 290, 9), (70, 292, 9), (70, 173, 9), (70, 196, 9), (70, 207, 9), (70, 246, 9), (72, 293, 9), (111, 293, 9), (145, 293, 9), (158, 293, 9), (170, 293, 9), (15, 293, 9), (68, 292, 9), (68, 326, 9), (68, 176, 9), (68, 186, 9), (68, 216, 9), (74, 232, 9), (118, 232, 9), (122, 232, 9), (148, 232, 9), (149, 232, 9), (159, 232, 9), (55, 232, 9), (74, 172, 9), (118, 172, 9), (122, 172, 9)],
    [(125, 172, 9), (138, 172, 9), (142, 172, 9), (148, 172, 9), (153, 172, 9), (159, 172, 9), (165, 172, 9), (168, 172, 9), (16, 172, 9), (55, 172, 9), (57, 172, 9), (43, 257, 8), (6, 257, 19), (43, 328, 8), (43, 328, 18), (6, 328, 21), (52, 174, 9), (145, 328, 9), (44, 290, 9), (7, 310, 9), (44, 317, 9), (7, 325, 9), (7, 173, 9), (44, 174, 9), (44, 179, 9), (7, 184, 9), (44, 188, 9), (44, 196, 9), (44, 207, 9), (44, 208, 9), (44, 212, 9), (7, 246, 9)],
    [(44, 256, 9), (68, 193, 9), (145, 193, 9), (44, 321, 9), (44, 182, 9), (44, 198, 9), (145, 191, 9), (44, 191, 5), (44, 191, 10), (109, 191, 12), (109, 191, 15), (109, 191, 19), (44, 322, 9), (78, 173, 9), (78, 184, 9), (78, 223, 9), (78, 226, 9), (78, 246, 9), (44, 322, 8), (78, 173, 8), (44, 174, 8), (44, 178, 8), (78, 184, 8), (44, 196, 8), (44, 198, 8), (44, 207, 8), (78, 223, 8), (44, 226, 8), (44, 246, 8), (108, 292, 8), (118, 292, 8), (134, 292, 8)],
    [(140, 292, 8), (145, 292, 8), (148, 292, 8), (31, 292, 8), (47, 292, 8), (55, 292, 8), (109, 327, 19), (77, 292, 7), (77, 290, 14), (77, 320, 14), (77, 173, 14), (77, 174, 14), (77, 178, 14), (77, 184, 14), (77, 196, 14), (77, 198, 14), (77, 207, 14), (77, 223, 14), (77, 226, 14), (77, 234, 14), (77, 239, 14), (77, 246, 14), (82, 292, 14), (108, 292, 14), (118, 292, 14), (125, 292, 14), (134, 292, 14), (138, 292, 14), (140, 292, 14), (142, 292, 14), (145, 292, 14), (148, 292, 14)],
    [(153, 292, 14), (165, 292, 14), (168, 292, 14), (16, 292, 14), (31, 292, 14), (47, 292, 14), (55, 292, 14), (57, 292, 14), (77, 222, 13), (77, 222, 1), (77, 222, 26), (77, 327, 28), (77, 327, 17), (77, 327, 19), (80, 290, 5), (80, 292, 5), (80, 310, 5), (80, 317, 5), (80, 325, 5), (80, 328, 5), (80, 173, 5), (80, 174, 5), (80, 179, 5), (80, 184, 5), (80, 188, 5), (80, 196, 5), (80, 207, 5), (80, 208, 5), (80, 212, 5), (80, 234, 5), (80, 239, 5), (80, 246, 5)],
    [(80, 256, 5), (68, 293, 5), (118, 293, 5), (124, 293, 5), (125, 293, 5), (138, 293, 5), (142, 293, 5), (145, 293, 5), (148, 293, 5), (149, 293, 5), (153, 293, 5), (165, 293, 5), (168, 293, 5), (16, 293, 5), (55, 293, 5), (57, 293, 5), (80, 327, 11), (80, 327, 15), (80, 327, 19), (52, 257, 7), (52, 257, 14), (52, 174, 17), (6, 184, 17), (84, 257, 17), (145, 257, 17), (44, 257, 17), (144, 289, 9), (43, 307, 9), (43, 180, 9), (144, 184, 9), (43, 201, 9), (43, 205, 9)],
    [(43, 228, 9), (144, 230, 9), (78, 291, 9), (86, 291, 9), (109, 291, 9), (120, 291, 9), (132, 291, 9), (134, 291, 9), (140, 291, 9), (145, 291, 9), (146, 291, 9), (31, 291, 9), (47, 291, 9), (44, 295, 9), (44, 184, 9), (44, 215, 9), (44, 223, 9), (44, 230, 9), (78, 257, 9), (107, 291, 9), (136, 291, 9), (164, 291, 9), (18, 291, 9), (50, 291, 9), (43, 184, 9), (43, 291, 8), (43, 197, 18), (144, 197, 21), (84, 295, 9), (43, 303, 9), (84, 184, 9), (84, 215, 9)],
    [(84, 230, 9), (98, 291, 9), (43, 328, 20), (144, 328, 23), (52, 184, 9), (44, 257, 8), (44, 197, 18), (44, 197, 20), (44, 197, 22), (44, 197, 2), (44, 327, 4), (44, 197, 29), (44, 295, 31), (44, 314, 31), (44, 174, 31), (44, 184, 31), (44, 215, 31), (44, 230, 31), (79, 197, 31), (107, 197, 31), (132, 197, 31), (136, 197, 31), (145, 197, 31), (146, 197, 31), (164, 197, 31), (18, 197, 31), (50, 197, 31), (80, 197, 9), (44, 291, 8), (84, 291, 8), (144, 289, 19), (44, 321, 19)],
    [(44, 174, 19), (44, 180, 19), (44, 182, 19), (144, 184, 19), (44, 198, 19), (44, 201, 19), (44, 205, 19), (144, 223, 19), (44, 226, 19), (44, 228, 19), (144, 230, 19), (78, 291, 19), (86, 291, 19), (109, 291, 19), (120, 291, 19), (132, 291, 19), (134, 291, 19), (140, 291, 19), (145, 291, 19), (146, 291, 19), (31, 291, 19), (47, 291, 19), (44, 257, 18), (84, 295, 21), (44, 321, 21), (44, 174, 21), (44, 182, 21), (84, 184, 21), (44, 198, 21), (84, 215, 21), (84, 223, 21), (84, 226, 21)],
    [(84, 230, 21), (78, 257, 21), (86, 257, 21), (107, 257, 21), (109, 257, 21), (132, 257, 21), (134, 257, 21), (136, 257, 21), (140, 257, 21), (145, 257, 21), (146, 257, 21), (164, 257, 21), (18, 257, 21), (31, 257, 21), (47, 257, 21), (50, 257, 21), (84, 174, 19), (9, 184, 19), (80, 328, 19), (84, 312, 19), (84, 180, 19), (84, 201, 19), (84, 205, 19), (84, 228, 19), (9, 230, 19), (98, 257, 19), (120, 257, 19), (132, 257, 19), (145, 257, 19), (146, 257, 19), (84, 295, 19), (84, 314, 19)],
    [(84, 184, 19), (84, 215, 19), (84, 230, 19), (98, 294, 19), (107, 294, 19), (132, 294, 19), (136, 294, 19), (145, 294, 19), (146, 294, 19), (164, 294, 19), (18, 294, 19), (50, 294, 19), (80, 294, 19)]
  ]


private def proofLookup0Fast (i : ℕ) : Option LateProofNode :=
  (proofBlocks[i / 32]?).bind (fun xs => xs[i % 32]?)

private def witnessLookup0Fast (i : ℕ) : Option WKey :=
  (witnessBlocks[i / 32]?).bind (fun xs => xs[i % 32]?)

private def lookupProofFast (pid : ℕ) : Option LateProofNode :=
  if 0 < pid ∧ pid ≤ 1090 then proofLookup0Fast (pid - 1) else none

private def lookupWitnessFast (wid : ℕ) : Option WKey :=
  if 0 < wid ∧ wid ≤ 1069 then witnessLookup0Fast (wid - 1) else none

private def fastMetadata : IndexMetadata :=
  { otherMetadata with
    proofNode := lookupProofFast
    witnessKey := fun wid => (lookupWitnessFast wid).map decodeWitness }

private theorem range_map_lookup {α : Type} (f : ℕ → Option α)
    (n : ℕ) (xs : List α) (h : (List.range n).map f = xs.map some)
    (i : ℕ) (hi : i < n) : f i = xs[i]? := by
  have he := congrArg (fun ys : List (Option α) => ys[i]?) h
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some] at he
  cases hx : xs[i]? with
  | none => simp only [hx, Option.map_none, Option.some_ne_none] at he
  | some x =>
    exact Option.some.inj (by simpa only [hx, Option.map_some] using he)

private theorem proof_range_map :
    (List.range 1090).map proofLookup0Fast = proofNodes.map some := by rfl

private theorem witness_range_map :
    (List.range 1069).map witnessLookup0Fast = witnessKeys.map some := by rfl

private theorem lookupProofFast_eq (pid : ℕ) : lookupProofFast pid = lookupProof pid := by
  by_cases hp : 0 < pid ∧ pid ≤ 1090
  · simp only [lookupProofFast, lookupProof, if_pos hp]
    exact range_map_lookup proofLookup0Fast 1090 proofNodes proof_range_map (pid - 1) (by omega)
  · simp only [lookupProofFast, lookupProof, if_neg hp]

private theorem lookupWitnessFast_eq (wid : ℕ) : lookupWitnessFast wid = lookupWitness wid := by
  by_cases hw : 0 < wid ∧ wid ≤ 1069
  · simp only [lookupWitnessFast, lookupWitness, if_pos hw]
    exact range_map_lookup witnessLookup0Fast 1069 witnessKeys witness_range_map (wid - 1) (by omega)
  · simp only [lookupWitnessFast, lookupWitness, if_neg hw]

private theorem fastMetadata_eq : fastMetadata = otherMetadata := by
  unfold fastMetadata
  rw [show lookupProofFast = lookupProof from funext lookupProofFast_eq,
    show lookupWitnessFast = lookupWitness from funext lookupWitnessFast_eq]
  rfl

private theorem checkDecision_cut_of (D : IndexMetadata) (side : Bool)
    (ids : List ℕ) (rid bid neg : ℕ) (left right : LateDecisionTree)
    (hbid : 0 < bid ∧ bid ≤ D.boundCount)
    (hcomp : D.complement bid = some neg)
    (hleft : checkDecision D side (bid :: ids) rid left = true)
    (hright : checkDecision D side (neg :: ids) rid right = true) :
    checkDecision D side ids rid (.cut bid left right) = true := by
  change (decide (0 < bid ∧ bid ≤ D.boundCount) &&
    match D.complement bid with
    | none => false
    | some n => checkDecision D side (bid :: ids) rid left &&
        checkDecision D side (n :: ids) rid right) = true
  apply Bool.and_eq_true_iff.mpr
  constructor
  · exact decide_eq_true_iff.mpr hbid
  · rw [hcomp]
    exact Bool.and_eq_true_iff.mpr ⟨hleft, hright⟩

private theorem checkDecision_split_of (D : IndexMetadata) (side : Bool)
    (ids : List ℕ) (rid l r : ℕ) (axis : Bool) (left right : LateDecisionTree)
    (hl : D.rectChild rid axis false = some l)
    (hr : D.rectChild rid axis true = some r)
    (hleft : checkDecision D side ids l left = true)
    (hright : checkDecision D side ids r right = true) :
    checkDecision D side ids rid (.split axis left right) = true := by
  change checkRectPair D rid axis
    (fun child => checkDecision D side ids child left)
    (fun child => checkDecision D side ids child right) = true
  simp only [checkRectPair, hl, hr]
  exact Bool.and_eq_true_iff.mpr ⟨hleft, hright⟩

private theorem checkDecision_metadata_transport (D E : IndexMetadata)
    (hD : D = E) (side : Bool) (ids : List ℕ) (rid : ℕ)
    (tree : LateDecisionTree) (h : checkDecision D side ids rid tree = true) :
    checkDecision E side ids rid tree = true := by
  cases hD
  exact h

private theorem checkDecision_tree_transport (D : IndexMetadata) (side : Bool)
    (ids : List ℕ) (rid : ℕ) (a b : LateDecisionTree) (hab : a = b)
    (h : checkDecision D side ids rid a = true) :
    checkDecision D side ids rid b = true := by
  cases hab
  exact h

private def tree_n172 : LateDecisionTree := .path 49
private def tree_n171 : LateDecisionTree := .path 48
private def tree_n170 : LateDecisionTree := .cut 257 tree_n171 tree_n172
private def tree_n169 : LateDecisionTree := .path 47
private def tree_n168 : LateDecisionTree := .path 46
private def tree_n167 : LateDecisionTree := .cut 144 tree_n168 tree_n169
private def tree_n166 : LateDecisionTree := .cut 9 tree_n167 tree_n170
private def tree_n165 : LateDecisionTree := .path 45
private def tree_n164 : LateDecisionTree := .empty 1036
private def tree_n163 : LateDecisionTree := .split true tree_n164 tree_n165
private def tree_n162 : LateDecisionTree := .path 44
private def tree_n161 : LateDecisionTree := .cut 144 tree_n162 tree_n163
private def tree_n160 : LateDecisionTree := .cut 44 tree_n161 tree_n166
private def tree_n159 : LateDecisionTree := .empty 1011
private def tree_n158 : LateDecisionTree := .split true tree_n159 tree_n160
private def tree_n157 : LateDecisionTree := .empty 1008
private def tree_n156 : LateDecisionTree := .path 43
private def tree_n155 : LateDecisionTree := .cut 328 tree_n156 tree_n157
private def tree_n154 : LateDecisionTree := .path 42
private def tree_n153 : LateDecisionTree := .empty 991
private def tree_n152 : LateDecisionTree := .split true tree_n153 tree_n154
private def tree_n151 : LateDecisionTree := .empty 988
private def tree_n150 : LateDecisionTree := .split false tree_n151 tree_n152
private def tree_n149 : LateDecisionTree := .empty 987
private def tree_n148 : LateDecisionTree := .split true tree_n149 tree_n150
private def tree_n147 : LateDecisionTree := .empty 986
private def tree_n146 : LateDecisionTree := .split true tree_n147 tree_n148
private def tree_n145 : LateDecisionTree := .empty 985
private def tree_n144 : LateDecisionTree := .split true tree_n145 tree_n146
private def tree_n143 : LateDecisionTree := .empty 984
private def tree_n142 : LateDecisionTree := .split true tree_n143 tree_n144
private def tree_n141 : LateDecisionTree := .path 41
private def tree_n140 : LateDecisionTree := .cut 328 tree_n141 tree_n142
private def tree_n139 : LateDecisionTree := .cut 257 tree_n140 tree_n155
private def tree_n138 : LateDecisionTree := .cut 197 tree_n139 tree_n158
private def tree_n137 : LateDecisionTree := .empty 978
private def tree_n136 : LateDecisionTree := .path 40
private def tree_n135 : LateDecisionTree := .cut 257 tree_n136 tree_n137
private def tree_n134 : LateDecisionTree := .empty 967
private def tree_n133 : LateDecisionTree := .path 39
private def tree_n132 : LateDecisionTree := .cut 257 tree_n133 tree_n134
private def tree_n131 : LateDecisionTree := .cut 197 tree_n132 tree_n135
private def tree_n130 : LateDecisionTree := .path 38
private def tree_n129 : LateDecisionTree := .path 37
private def tree_n128 : LateDecisionTree := .cut 144 tree_n129 tree_n130
private def tree_n127 : LateDecisionTree := .cut 44 tree_n128 tree_n131
private def tree_n126 : LateDecisionTree := .cut 43 tree_n127 tree_n138
private def tree_n125 : LateDecisionTree := .empty 785
private def tree_n124 : LateDecisionTree := .path 36
private def tree_n123 : LateDecisionTree := .empty 930
private def tree_n122 : LateDecisionTree := .split true tree_n123 tree_n124
private def tree_n121 : LateDecisionTree := .empty 929
private def tree_n120 : LateDecisionTree := .split true tree_n121 tree_n122
private def tree_n119 : LateDecisionTree := .split true tree_n120 tree_n125
private def tree_n118 : LateDecisionTree := .empty 928
private def tree_n117 : LateDecisionTree := .empty 927
private def tree_n116 : LateDecisionTree := .empty 926
private def tree_n115 : LateDecisionTree := .path 35
private def tree_n114 : LateDecisionTree := .split true tree_n115 tree_n116
private def tree_n113 : LateDecisionTree := .split true tree_n114 tree_n117
private def tree_n112 : LateDecisionTree := .split true tree_n113 tree_n118
private def tree_n111 : LateDecisionTree := .empty 891
private def tree_n110 : LateDecisionTree := .empty 890
private def tree_n109 : LateDecisionTree := .empty 883
private def tree_n108 : LateDecisionTree := .path 34
private def tree_n107 : LateDecisionTree := .cut 109 tree_n108 tree_n109
private def tree_n106 : LateDecisionTree := .split true tree_n107 tree_n110
private def tree_n105 : LateDecisionTree := .empty 850
private def tree_n104 : LateDecisionTree := .split true tree_n105 tree_n106
private def tree_n103 : LateDecisionTree := .split true tree_n104 tree_n111
private def tree_n102 : LateDecisionTree := .empty 849
private def tree_n101 : LateDecisionTree := .path 33
private def tree_n100 : LateDecisionTree := .split true tree_n101 tree_n102
private def tree_n099 : LateDecisionTree := .path 32
private def tree_n098 : LateDecisionTree := .cut 222 tree_n099 tree_n100
private def tree_n097 : LateDecisionTree := .cut 190 tree_n098 tree_n103
private def tree_n096 : LateDecisionTree := .empty 814
private def tree_n095 : LateDecisionTree := .path 31
private def tree_n094 : LateDecisionTree := .cut 222 tree_n095 tree_n096
private def tree_n093 : LateDecisionTree := .cut 191 tree_n094 tree_n097
private def tree_n092 : LateDecisionTree := .path 30
private def tree_n091 : LateDecisionTree := .cut 7 tree_n092 tree_n093
private def tree_n090 : LateDecisionTree := .path 29
private def tree_n089 : LateDecisionTree := .cut 328 tree_n090 tree_n091
private def tree_n088 : LateDecisionTree := .cut 193 tree_n089 tree_n112
private def tree_n087 : LateDecisionTree := .cut 144 tree_n088 tree_n119
private def tree_n086 : LateDecisionTree := .empty 786
private def tree_n085 : LateDecisionTree := .empty 783
private def tree_n084 : LateDecisionTree := .path 28
private def tree_n083 : LateDecisionTree := .path 27
private def tree_n082 : LateDecisionTree := .cut 232 tree_n083 tree_n084
private def tree_n081 : LateDecisionTree := .path 26
private def tree_n080 : LateDecisionTree := .path 25
private def tree_n079 : LateDecisionTree := .cut 183 tree_n080 tree_n081
private def tree_n078 : LateDecisionTree := .cut 59 tree_n079 tree_n082
private def tree_n077 : LateDecisionTree := .empty 718
private def tree_n076 : LateDecisionTree := .path 24
private def tree_n075 : LateDecisionTree := .empty 690
private def tree_n074 : LateDecisionTree := .split true tree_n075 tree_n076
private def tree_n073 : LateDecisionTree := .split true tree_n074 tree_n077
private def tree_n072 : LateDecisionTree := .path 23
private def tree_n071 : LateDecisionTree := .cut 7 tree_n072 tree_n073
private def tree_n070 : LateDecisionTree := .path 22
private def tree_n069 : LateDecisionTree := .empty 639
private def tree_n068 : LateDecisionTree := .split true tree_n069 tree_n070
private def tree_n067 : LateDecisionTree := .path 21
private def tree_n066 : LateDecisionTree := .cut 232 tree_n067 tree_n068
private def tree_n065 : LateDecisionTree := .cut 222 tree_n066 tree_n071
private def tree_n064 : LateDecisionTree := .empty 627
private def tree_n063 : LateDecisionTree := .path 20
private def tree_n062 : LateDecisionTree := .empty 606
private def tree_n061 : LateDecisionTree := .split true tree_n062 tree_n063
private def tree_n060 : LateDecisionTree := .split true tree_n061 tree_n064
private def tree_n059 : LateDecisionTree := .path 19
private def tree_n058 : LateDecisionTree := .cut 222 tree_n059 tree_n060
private def tree_n057 : LateDecisionTree := .cut 190 tree_n058 tree_n065
private def tree_n056 : LateDecisionTree := .cut 181 tree_n057 tree_n078
private def tree_n055 : LateDecisionTree := .cut 144 tree_n056 tree_n085
private def tree_n054 : LateDecisionTree := .cut 44 tree_n055 tree_n086
private def tree_n053 : LateDecisionTree := .cut 43 tree_n054 tree_n087
private def tree_n052 : LateDecisionTree := .cut 6 tree_n053 tree_n126
private def tree_n051 : LateDecisionTree := .path 18
private def tree_n050 : LateDecisionTree := .path 17
private def tree_n049 : LateDecisionTree := .path 16
private def tree_n048 : LateDecisionTree := .cut 237 tree_n049 tree_n050
private def tree_n047 : LateDecisionTree := .path 15
private def tree_n046 : LateDecisionTree := .path 14
private def tree_n045 : LateDecisionTree := .cut 237 tree_n046 tree_n047
private def tree_n044 : LateDecisionTree := .cut 183 tree_n045 tree_n048
private def tree_n043 : LateDecisionTree := .cut 43 tree_n044 tree_n051
private def tree_n042 : LateDecisionTree := .path 13
private def tree_n041 : LateDecisionTree := .path 12
private def tree_n040 : LateDecisionTree := .path 11
private def tree_n039 : LateDecisionTree := .path 10
private def tree_n038 : LateDecisionTree := .empty 318
private def tree_n037 : LateDecisionTree := .split false tree_n038 tree_n039
private def tree_n036 : LateDecisionTree := .empty 317
private def tree_n035 : LateDecisionTree := .split true tree_n036 tree_n037
private def tree_n034 : LateDecisionTree := .empty 316
private def tree_n033 : LateDecisionTree := .split false tree_n034 tree_n035
private def tree_n032 : LateDecisionTree := .empty 315
private def tree_n031 : LateDecisionTree := .split true tree_n032 tree_n033
private def tree_n030 : LateDecisionTree := .empty 314
private def tree_n029 : LateDecisionTree := .split true tree_n030 tree_n031
private def tree_n028 : LateDecisionTree := .empty 313
private def tree_n027 : LateDecisionTree := .split true tree_n028 tree_n029
private def tree_n026 : LateDecisionTree := .empty 312
private def tree_n025 : LateDecisionTree := .split true tree_n026 tree_n027
private def tree_n024 : LateDecisionTree := .path 9
private def tree_n023 : LateDecisionTree := .cut 259 tree_n024 tree_n025
private def tree_n022 : LateDecisionTree := .cut 151 tree_n023 tree_n040
private def tree_n021 : LateDecisionTree := .path 8
private def tree_n020 : LateDecisionTree := .path 7
private def tree_n019 : LateDecisionTree := .cut 194 tree_n020 tree_n021
private def tree_n018 : LateDecisionTree := .path 6
private def tree_n017 : LateDecisionTree := .cut 265 tree_n018 tree_n019
private def tree_n016 : LateDecisionTree := .cut 206 tree_n017 tree_n022
private def tree_n015 : LateDecisionTree := .path 5
private def tree_n014 : LateDecisionTree := .path 4
private def tree_n013 : LateDecisionTree := .cut 145 tree_n014 tree_n015
private def tree_n012 : LateDecisionTree := .path 3
private def tree_n011 : LateDecisionTree := .cut 202 tree_n012 tree_n013
private def tree_n010 : LateDecisionTree := .path 2
private def tree_n009 : LateDecisionTree := .cut 194 tree_n010 tree_n011
private def tree_n008 : LateDecisionTree := .empty 50
private def tree_n007 : LateDecisionTree := .path 1
private def tree_n006 : LateDecisionTree := .cut 259 tree_n007 tree_n008
private def tree_n005 : LateDecisionTree := .cut 12 tree_n006 tree_n009
private def tree_n004 : LateDecisionTree := .cut 149 tree_n005 tree_n016
private def tree_n003 : LateDecisionTree := .cut 14 tree_n004 tree_n041
private def tree_n002 : LateDecisionTree := .cut 137 tree_n003 tree_n042
private def tree_n001 : LateDecisionTree := .cut 11 tree_n002 tree_n043
private def tree_n000 : LateDecisionTree := .cut 8 tree_n001 tree_n052

private theorem generated_tree_exact : tree_n000 = lateTree false := by rfl

private theorem tree_n172_checked :
    checkDecision fastMetadata false [144, 294, 328, 84, 327, 291, 293, 17, 52, 258] 19 tree_n172 = true := by
  decide +kernel

private theorem tree_n171_checked :
    checkDecision fastMetadata false [257, 294, 328, 84, 327, 291, 293, 17, 52, 258] 19 tree_n171 = true := by
  decide +kernel

private theorem tree_n170_checked :
    checkDecision fastMetadata false [294, 328, 84, 327, 291, 293, 17, 52, 258] 19 tree_n170 = true := by
  refine checkDecision_tree_transport fastMetadata false [294, 328, 84, 327, 291, 293, 17, 52, 258] 19
    (.cut 257 tree_n171 tree_n172) tree_n170 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [294, 328, 84, 327, 291, 293, 17, 52, 258] 19 257 144
    tree_n171 tree_n172 (by decide +kernel) (by decide +kernel)
    tree_n171_checked tree_n172_checked

private theorem tree_n169_checked :
    checkDecision fastMetadata false [257, 9, 328, 84, 327, 291, 293, 17, 52, 258] 19 tree_n169 = true := by
  decide +kernel

private theorem tree_n168_checked :
    checkDecision fastMetadata false [144, 9, 328, 84, 327, 291, 293, 17, 52, 258] 19 tree_n168 = true := by
  decide +kernel

private theorem tree_n167_checked :
    checkDecision fastMetadata false [9, 328, 84, 327, 291, 293, 17, 52, 258] 19 tree_n167 = true := by
  refine checkDecision_tree_transport fastMetadata false [9, 328, 84, 327, 291, 293, 17, 52, 258] 19
    (.cut 144 tree_n168 tree_n169) tree_n167 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [9, 328, 84, 327, 291, 293, 17, 52, 258] 19 144 257
    tree_n168 tree_n169 (by decide +kernel) (by decide +kernel)
    tree_n168_checked tree_n169_checked

private theorem tree_n166_checked :
    checkDecision fastMetadata false [328, 84, 327, 291, 293, 17, 52, 258] 19 tree_n166 = true := by
  refine checkDecision_tree_transport fastMetadata false [328, 84, 327, 291, 293, 17, 52, 258] 19
    (.cut 9 tree_n167 tree_n170) tree_n166 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [328, 84, 327, 291, 293, 17, 52, 258] 19 9 294
    tree_n167 tree_n170 (by decide +kernel) (by decide +kernel)
    tree_n167_checked tree_n170_checked

private theorem tree_n165_checked :
    checkDecision fastMetadata false [257, 44, 84, 327, 291, 293, 17, 52, 258] 21 tree_n165 = true := by
  decide +kernel

private theorem tree_n164_checked :
    checkDecision fastMetadata false [257, 44, 84, 327, 291, 293, 17, 52, 258] 18 tree_n164 = true := by
  decide +kernel

private theorem tree_n163_checked :
    checkDecision fastMetadata false [257, 44, 84, 327, 291, 293, 17, 52, 258] 19 tree_n163 = true := by
  refine checkDecision_tree_transport fastMetadata false [257, 44, 84, 327, 291, 293, 17, 52, 258] 19
    (.split true tree_n164 tree_n165) tree_n163 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [257, 44, 84, 327, 291, 293, 17, 52, 258] 19 18 21
    true tree_n164 tree_n165 (by decide +kernel) (by decide +kernel)
    tree_n164_checked tree_n165_checked

private theorem tree_n162_checked :
    checkDecision fastMetadata false [144, 44, 84, 327, 291, 293, 17, 52, 258] 19 tree_n162 = true := by
  decide +kernel

private theorem tree_n161_checked :
    checkDecision fastMetadata false [44, 84, 327, 291, 293, 17, 52, 258] 19 tree_n161 = true := by
  refine checkDecision_tree_transport fastMetadata false [44, 84, 327, 291, 293, 17, 52, 258] 19
    (.cut 144 tree_n162 tree_n163) tree_n161 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [44, 84, 327, 291, 293, 17, 52, 258] 19 144 257
    tree_n162 tree_n163 (by decide +kernel) (by decide +kernel)
    tree_n162_checked tree_n163_checked

private theorem tree_n160_checked :
    checkDecision fastMetadata false [84, 327, 291, 293, 17, 52, 258] 19 tree_n160 = true := by
  refine checkDecision_tree_transport fastMetadata false [84, 327, 291, 293, 17, 52, 258] 19
    (.cut 44 tree_n161 tree_n166) tree_n160 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [84, 327, 291, 293, 17, 52, 258] 19 44 328
    tree_n161 tree_n166 (by decide +kernel) (by decide +kernel)
    tree_n161_checked tree_n166_checked

private theorem tree_n159_checked :
    checkDecision fastMetadata false [84, 327, 291, 293, 17, 52, 258] 8 tree_n159 = true := by
  decide +kernel

private theorem tree_n158_checked :
    checkDecision fastMetadata false [84, 327, 291, 293, 17, 52, 258] 9 tree_n158 = true := by
  refine checkDecision_tree_transport fastMetadata false [84, 327, 291, 293, 17, 52, 258] 9
    (.split true tree_n159 tree_n160) tree_n158 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [84, 327, 291, 293, 17, 52, 258] 9 8 19
    true tree_n159 tree_n160 (by decide +kernel) (by decide +kernel)
    tree_n159_checked tree_n160_checked

private theorem tree_n157_checked :
    checkDecision fastMetadata false [44, 144, 197, 327, 291, 293, 17, 52, 258] 9 tree_n157 = true := by
  decide +kernel

private theorem tree_n156_checked :
    checkDecision fastMetadata false [328, 144, 197, 327, 291, 293, 17, 52, 258] 9 tree_n156 = true := by
  decide +kernel

private theorem tree_n155_checked :
    checkDecision fastMetadata false [144, 197, 327, 291, 293, 17, 52, 258] 9 tree_n155 = true := by
  refine checkDecision_tree_transport fastMetadata false [144, 197, 327, 291, 293, 17, 52, 258] 9
    (.cut 328 tree_n156 tree_n157) tree_n155 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [144, 197, 327, 291, 293, 17, 52, 258] 9 328 44
    tree_n156 tree_n157 (by decide +kernel) (by decide +kernel)
    tree_n156_checked tree_n157_checked

private theorem tree_n154_checked :
    checkDecision fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 31 tree_n154 = true := by
  decide +kernel

private theorem tree_n153_checked :
    checkDecision fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 29 tree_n153 = true := by
  decide +kernel

private theorem tree_n152_checked :
    checkDecision fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 30 tree_n152 = true := by
  refine checkDecision_tree_transport fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 30
    (.split true tree_n153 tree_n154) tree_n152 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 30 29 31
    true tree_n153 tree_n154 (by decide +kernel) (by decide +kernel)
    tree_n153_checked tree_n154_checked

private theorem tree_n151_checked :
    checkDecision fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 3 tree_n151 = true := by
  decide +kernel

private theorem tree_n150_checked :
    checkDecision fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 24 tree_n150 = true := by
  refine checkDecision_tree_transport fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 24
    (.split false tree_n151 tree_n152) tree_n150 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 24 3 30
    false tree_n151 tree_n152 (by decide +kernel) (by decide +kernel)
    tree_n151_checked tree_n152_checked

private theorem tree_n149_checked :
    checkDecision fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 22 tree_n149 = true := by
  decide +kernel

private theorem tree_n148_checked :
    checkDecision fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 23 tree_n148 = true := by
  refine checkDecision_tree_transport fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 23
    (.split true tree_n149 tree_n150) tree_n148 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 23 22 24
    true tree_n149 tree_n150 (by decide +kernel) (by decide +kernel)
    tree_n149_checked tree_n150_checked

private theorem tree_n147_checked :
    checkDecision fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 20 tree_n147 = true := by
  decide +kernel

private theorem tree_n146_checked :
    checkDecision fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 21 tree_n146 = true := by
  refine checkDecision_tree_transport fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 21
    (.split true tree_n147 tree_n148) tree_n146 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 21 20 23
    true tree_n147 tree_n148 (by decide +kernel) (by decide +kernel)
    tree_n147_checked tree_n148_checked

private theorem tree_n145_checked :
    checkDecision fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 18 tree_n145 = true := by
  decide +kernel

private theorem tree_n144_checked :
    checkDecision fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 19 tree_n144 = true := by
  refine checkDecision_tree_transport fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 19
    (.split true tree_n145 tree_n146) tree_n144 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 19 18 21
    true tree_n145 tree_n146 (by decide +kernel) (by decide +kernel)
    tree_n145_checked tree_n146_checked

private theorem tree_n143_checked :
    checkDecision fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 8 tree_n143 = true := by
  decide +kernel

private theorem tree_n142_checked :
    checkDecision fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 9 tree_n142 = true := by
  refine checkDecision_tree_transport fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 9
    (.split true tree_n143 tree_n144) tree_n142 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [44, 257, 197, 327, 291, 293, 17, 52, 258] 9 8 19
    true tree_n143 tree_n144 (by decide +kernel) (by decide +kernel)
    tree_n143_checked tree_n144_checked

private theorem tree_n141_checked :
    checkDecision fastMetadata false [328, 257, 197, 327, 291, 293, 17, 52, 258] 9 tree_n141 = true := by
  decide +kernel

private theorem tree_n140_checked :
    checkDecision fastMetadata false [257, 197, 327, 291, 293, 17, 52, 258] 9 tree_n140 = true := by
  refine checkDecision_tree_transport fastMetadata false [257, 197, 327, 291, 293, 17, 52, 258] 9
    (.cut 328 tree_n141 tree_n142) tree_n140 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [257, 197, 327, 291, 293, 17, 52, 258] 9 328 44
    tree_n141 tree_n142 (by decide +kernel) (by decide +kernel)
    tree_n141_checked tree_n142_checked

private theorem tree_n139_checked :
    checkDecision fastMetadata false [197, 327, 291, 293, 17, 52, 258] 9 tree_n139 = true := by
  refine checkDecision_tree_transport fastMetadata false [197, 327, 291, 293, 17, 52, 258] 9
    (.cut 257 tree_n140 tree_n155) tree_n139 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [197, 327, 291, 293, 17, 52, 258] 9 257 144
    tree_n140 tree_n155 (by decide +kernel) (by decide +kernel)
    tree_n140_checked tree_n155_checked

private theorem tree_n138_checked :
    checkDecision fastMetadata false [327, 291, 293, 17, 52, 258] 9 tree_n138 = true := by
  refine checkDecision_tree_transport fastMetadata false [327, 291, 293, 17, 52, 258] 9
    (.cut 197 tree_n139 tree_n158) tree_n138 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [327, 291, 293, 17, 52, 258] 9 197 84
    tree_n139 tree_n158 (by decide +kernel) (by decide +kernel)
    tree_n139_checked tree_n158_checked

private theorem tree_n137_checked :
    checkDecision fastMetadata false [144, 84, 328, 43, 291, 293, 17, 52, 258] 9 tree_n137 = true := by
  decide +kernel

private theorem tree_n136_checked :
    checkDecision fastMetadata false [257, 84, 328, 43, 291, 293, 17, 52, 258] 9 tree_n136 = true := by
  decide +kernel

private theorem tree_n135_checked :
    checkDecision fastMetadata false [84, 328, 43, 291, 293, 17, 52, 258] 9 tree_n135 = true := by
  refine checkDecision_tree_transport fastMetadata false [84, 328, 43, 291, 293, 17, 52, 258] 9
    (.cut 257 tree_n136 tree_n137) tree_n135 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [84, 328, 43, 291, 293, 17, 52, 258] 9 257 144
    tree_n136 tree_n137 (by decide +kernel) (by decide +kernel)
    tree_n136_checked tree_n137_checked

private theorem tree_n134_checked :
    checkDecision fastMetadata false [144, 197, 328, 43, 291, 293, 17, 52, 258] 9 tree_n134 = true := by
  decide +kernel

private theorem tree_n133_checked :
    checkDecision fastMetadata false [257, 197, 328, 43, 291, 293, 17, 52, 258] 9 tree_n133 = true := by
  decide +kernel

private theorem tree_n132_checked :
    checkDecision fastMetadata false [197, 328, 43, 291, 293, 17, 52, 258] 9 tree_n132 = true := by
  refine checkDecision_tree_transport fastMetadata false [197, 328, 43, 291, 293, 17, 52, 258] 9
    (.cut 257 tree_n133 tree_n134) tree_n132 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [197, 328, 43, 291, 293, 17, 52, 258] 9 257 144
    tree_n133 tree_n134 (by decide +kernel) (by decide +kernel)
    tree_n133_checked tree_n134_checked

private theorem tree_n131_checked :
    checkDecision fastMetadata false [328, 43, 291, 293, 17, 52, 258] 9 tree_n131 = true := by
  refine checkDecision_tree_transport fastMetadata false [328, 43, 291, 293, 17, 52, 258] 9
    (.cut 197 tree_n132 tree_n135) tree_n131 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [328, 43, 291, 293, 17, 52, 258] 9 197 84
    tree_n132 tree_n135 (by decide +kernel) (by decide +kernel)
    tree_n132_checked tree_n135_checked

private theorem tree_n130_checked :
    checkDecision fastMetadata false [257, 44, 43, 291, 293, 17, 52, 258] 9 tree_n130 = true := by
  decide +kernel

private theorem tree_n129_checked :
    checkDecision fastMetadata false [144, 44, 43, 291, 293, 17, 52, 258] 9 tree_n129 = true := by
  decide +kernel

private theorem tree_n128_checked :
    checkDecision fastMetadata false [44, 43, 291, 293, 17, 52, 258] 9 tree_n128 = true := by
  refine checkDecision_tree_transport fastMetadata false [44, 43, 291, 293, 17, 52, 258] 9
    (.cut 144 tree_n129 tree_n130) tree_n128 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [44, 43, 291, 293, 17, 52, 258] 9 144 257
    tree_n129 tree_n130 (by decide +kernel) (by decide +kernel)
    tree_n129_checked tree_n130_checked

private theorem tree_n127_checked :
    checkDecision fastMetadata false [43, 291, 293, 17, 52, 258] 9 tree_n127 = true := by
  refine checkDecision_tree_transport fastMetadata false [43, 291, 293, 17, 52, 258] 9
    (.cut 44 tree_n128 tree_n131) tree_n127 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [43, 291, 293, 17, 52, 258] 9 44 328
    tree_n128 tree_n131 (by decide +kernel) (by decide +kernel)
    tree_n128_checked tree_n131_checked

private theorem tree_n126_checked :
    checkDecision fastMetadata false [291, 293, 17, 52, 258] 9 tree_n126 = true := by
  refine checkDecision_tree_transport fastMetadata false [291, 293, 17, 52, 258] 9
    (.cut 43 tree_n127 tree_n138) tree_n126 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [291, 293, 17, 52, 258] 9 43 327
    tree_n127 tree_n138 (by decide +kernel) (by decide +kernel)
    tree_n127_checked tree_n138_checked

private theorem tree_n125_checked :
    checkDecision fastMetadata false [257, 327, 6, 293, 17, 52, 258] 19 tree_n125 = true := by
  decide +kernel

private theorem tree_n124_checked :
    checkDecision fastMetadata false [257, 327, 6, 293, 17, 52, 258] 17 tree_n124 = true := by
  decide +kernel

private theorem tree_n123_checked :
    checkDecision fastMetadata false [257, 327, 6, 293, 17, 52, 258] 14 tree_n123 = true := by
  decide +kernel

private theorem tree_n122_checked :
    checkDecision fastMetadata false [257, 327, 6, 293, 17, 52, 258] 15 tree_n122 = true := by
  refine checkDecision_tree_transport fastMetadata false [257, 327, 6, 293, 17, 52, 258] 15
    (.split true tree_n123 tree_n124) tree_n122 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [257, 327, 6, 293, 17, 52, 258] 15 14 17
    true tree_n123 tree_n124 (by decide +kernel) (by decide +kernel)
    tree_n123_checked tree_n124_checked

private theorem tree_n121_checked :
    checkDecision fastMetadata false [257, 327, 6, 293, 17, 52, 258] 7 tree_n121 = true := by
  decide +kernel

private theorem tree_n120_checked :
    checkDecision fastMetadata false [257, 327, 6, 293, 17, 52, 258] 8 tree_n120 = true := by
  refine checkDecision_tree_transport fastMetadata false [257, 327, 6, 293, 17, 52, 258] 8
    (.split true tree_n121 tree_n122) tree_n120 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [257, 327, 6, 293, 17, 52, 258] 8 7 15
    true tree_n121 tree_n122 (by decide +kernel) (by decide +kernel)
    tree_n121_checked tree_n122_checked

private theorem tree_n119_checked :
    checkDecision fastMetadata false [257, 327, 6, 293, 17, 52, 258] 9 tree_n119 = true := by
  refine checkDecision_tree_transport fastMetadata false [257, 327, 6, 293, 17, 52, 258] 9
    (.split true tree_n120 tree_n125) tree_n119 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [257, 327, 6, 293, 17, 52, 258] 9 8 19
    true tree_n120 tree_n125 (by decide +kernel) (by decide +kernel)
    tree_n120_checked tree_n125_checked

private theorem tree_n118_checked :
    checkDecision fastMetadata false [80, 144, 327, 6, 293, 17, 52, 258] 19 tree_n118 = true := by
  decide +kernel

private theorem tree_n117_checked :
    checkDecision fastMetadata false [80, 144, 327, 6, 293, 17, 52, 258] 15 tree_n117 = true := by
  decide +kernel

private theorem tree_n116_checked :
    checkDecision fastMetadata false [80, 144, 327, 6, 293, 17, 52, 258] 11 tree_n116 = true := by
  decide +kernel

private theorem tree_n115_checked :
    checkDecision fastMetadata false [80, 144, 327, 6, 293, 17, 52, 258] 5 tree_n115 = true := by
  decide +kernel

private theorem tree_n114_checked :
    checkDecision fastMetadata false [80, 144, 327, 6, 293, 17, 52, 258] 7 tree_n114 = true := by
  refine checkDecision_tree_transport fastMetadata false [80, 144, 327, 6, 293, 17, 52, 258] 7
    (.split true tree_n115 tree_n116) tree_n114 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [80, 144, 327, 6, 293, 17, 52, 258] 7 5 11
    true tree_n115 tree_n116 (by decide +kernel) (by decide +kernel)
    tree_n115_checked tree_n116_checked

private theorem tree_n113_checked :
    checkDecision fastMetadata false [80, 144, 327, 6, 293, 17, 52, 258] 8 tree_n113 = true := by
  refine checkDecision_tree_transport fastMetadata false [80, 144, 327, 6, 293, 17, 52, 258] 8
    (.split true tree_n114 tree_n117) tree_n113 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [80, 144, 327, 6, 293, 17, 52, 258] 8 7 15
    true tree_n114 tree_n117 (by decide +kernel) (by decide +kernel)
    tree_n114_checked tree_n117_checked

private theorem tree_n112_checked :
    checkDecision fastMetadata false [80, 144, 327, 6, 293, 17, 52, 258] 9 tree_n112 = true := by
  refine checkDecision_tree_transport fastMetadata false [80, 144, 327, 6, 293, 17, 52, 258] 9
    (.split true tree_n113 tree_n118) tree_n112 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [80, 144, 327, 6, 293, 17, 52, 258] 9 8 19
    true tree_n113 tree_n118 (by decide +kernel) (by decide +kernel)
    tree_n113_checked tree_n118_checked

private theorem tree_n111_checked :
    checkDecision fastMetadata false [77, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 19 tree_n111 = true := by
  decide +kernel

private theorem tree_n110_checked :
    checkDecision fastMetadata false [77, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 17 tree_n110 = true := by
  decide +kernel

private theorem tree_n109_checked :
    checkDecision fastMetadata false [222, 77, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 14 tree_n109 = true := by
  decide +kernel

private theorem tree_n108_checked :
    checkDecision fastMetadata false [109, 77, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 14 tree_n108 = true := by
  decide +kernel

private theorem tree_n107_checked :
    checkDecision fastMetadata false [77, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 14 tree_n107 = true := by
  refine checkDecision_tree_transport fastMetadata false [77, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 14
    (.cut 109 tree_n108 tree_n109) tree_n107 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [77, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 14 109 222
    tree_n108 tree_n109 (by decide +kernel) (by decide +kernel)
    tree_n108_checked tree_n109_checked

private theorem tree_n106_checked :
    checkDecision fastMetadata false [77, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 15 tree_n106 = true := by
  refine checkDecision_tree_transport fastMetadata false [77, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 15
    (.split true tree_n107 tree_n110) tree_n106 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [77, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 15 14 17
    true tree_n107 tree_n110 (by decide +kernel) (by decide +kernel)
    tree_n107_checked tree_n110_checked

private theorem tree_n105_checked :
    checkDecision fastMetadata false [77, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 7 tree_n105 = true := by
  decide +kernel

private theorem tree_n104_checked :
    checkDecision fastMetadata false [77, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 8 tree_n104 = true := by
  refine checkDecision_tree_transport fastMetadata false [77, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 8
    (.split true tree_n105 tree_n106) tree_n104 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [77, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 8 7 15
    true tree_n105 tree_n106 (by decide +kernel) (by decide +kernel)
    tree_n105_checked tree_n106_checked

private theorem tree_n103_checked :
    checkDecision fastMetadata false [77, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 9 tree_n103 = true := by
  refine checkDecision_tree_transport fastMetadata false [77, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 9
    (.split true tree_n104 tree_n111) tree_n103 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [77, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 9 8 19
    true tree_n104 tree_n111 (by decide +kernel) (by decide +kernel)
    tree_n104_checked tree_n111_checked

private theorem tree_n102_checked :
    checkDecision fastMetadata false [109, 190, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 19 tree_n102 = true := by
  decide +kernel

private theorem tree_n101_checked :
    checkDecision fastMetadata false [109, 190, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 8 tree_n101 = true := by
  decide +kernel

private theorem tree_n100_checked :
    checkDecision fastMetadata false [109, 190, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 9 tree_n100 = true := by
  refine checkDecision_tree_transport fastMetadata false [109, 190, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 9
    (.split true tree_n101 tree_n102) tree_n100 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [109, 190, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 9 8 19
    true tree_n101 tree_n102 (by decide +kernel) (by decide +kernel)
    tree_n101_checked tree_n102_checked

private theorem tree_n099_checked :
    checkDecision fastMetadata false [222, 190, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 9 tree_n099 = true := by
  decide +kernel

private theorem tree_n098_checked :
    checkDecision fastMetadata false [190, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 9 tree_n098 = true := by
  refine checkDecision_tree_transport fastMetadata false [190, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 9
    (.cut 222 tree_n099 tree_n100) tree_n098 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [190, 78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 9 222 109
    tree_n099 tree_n100 (by decide +kernel) (by decide +kernel)
    tree_n099_checked tree_n100_checked

private theorem tree_n097_checked :
    checkDecision fastMetadata false [78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 9 tree_n097 = true := by
  refine checkDecision_tree_transport fastMetadata false [78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 9
    (.cut 190 tree_n098 tree_n103) tree_n097 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [78, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 9 190 77
    tree_n098 tree_n103 (by decide +kernel) (by decide +kernel)
    tree_n098_checked tree_n103_checked

private theorem tree_n096_checked :
    checkDecision fastMetadata false [109, 191, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 9 tree_n096 = true := by
  decide +kernel

private theorem tree_n095_checked :
    checkDecision fastMetadata false [222, 191, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 9 tree_n095 = true := by
  decide +kernel

private theorem tree_n094_checked :
    checkDecision fastMetadata false [191, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 9 tree_n094 = true := by
  refine checkDecision_tree_transport fastMetadata false [191, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 9
    (.cut 222 tree_n095 tree_n096) tree_n094 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [191, 292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 9 222 109
    tree_n095 tree_n096 (by decide +kernel) (by decide +kernel)
    tree_n095_checked tree_n096_checked

private theorem tree_n093_checked :
    checkDecision fastMetadata false [292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 9 tree_n093 = true := by
  refine checkDecision_tree_transport fastMetadata false [292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 9
    (.cut 191 tree_n094 tree_n097) tree_n093 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [292, 44, 193, 144, 327, 6, 293, 17, 52, 258] 9 191 78
    tree_n094 tree_n097 (by decide +kernel) (by decide +kernel)
    tree_n094_checked tree_n097_checked

private theorem tree_n092_checked :
    checkDecision fastMetadata false [7, 44, 193, 144, 327, 6, 293, 17, 52, 258] 9 tree_n092 = true := by
  decide +kernel

private theorem tree_n091_checked :
    checkDecision fastMetadata false [44, 193, 144, 327, 6, 293, 17, 52, 258] 9 tree_n091 = true := by
  refine checkDecision_tree_transport fastMetadata false [44, 193, 144, 327, 6, 293, 17, 52, 258] 9
    (.cut 7 tree_n092 tree_n093) tree_n091 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [44, 193, 144, 327, 6, 293, 17, 52, 258] 9 7 292
    tree_n092 tree_n093 (by decide +kernel) (by decide +kernel)
    tree_n092_checked tree_n093_checked

private theorem tree_n090_checked :
    checkDecision fastMetadata false [328, 193, 144, 327, 6, 293, 17, 52, 258] 9 tree_n090 = true := by
  decide +kernel

private theorem tree_n089_checked :
    checkDecision fastMetadata false [193, 144, 327, 6, 293, 17, 52, 258] 9 tree_n089 = true := by
  refine checkDecision_tree_transport fastMetadata false [193, 144, 327, 6, 293, 17, 52, 258] 9
    (.cut 328 tree_n090 tree_n091) tree_n089 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [193, 144, 327, 6, 293, 17, 52, 258] 9 328 44
    tree_n090 tree_n091 (by decide +kernel) (by decide +kernel)
    tree_n090_checked tree_n091_checked

private theorem tree_n088_checked :
    checkDecision fastMetadata false [144, 327, 6, 293, 17, 52, 258] 9 tree_n088 = true := by
  refine checkDecision_tree_transport fastMetadata false [144, 327, 6, 293, 17, 52, 258] 9
    (.cut 193 tree_n089 tree_n112) tree_n088 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [144, 327, 6, 293, 17, 52, 258] 9 193 80
    tree_n089 tree_n112 (by decide +kernel) (by decide +kernel)
    tree_n089_checked tree_n112_checked

private theorem tree_n087_checked :
    checkDecision fastMetadata false [327, 6, 293, 17, 52, 258] 9 tree_n087 = true := by
  refine checkDecision_tree_transport fastMetadata false [327, 6, 293, 17, 52, 258] 9
    (.cut 144 tree_n088 tree_n119) tree_n087 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [327, 6, 293, 17, 52, 258] 9 144 257
    tree_n088 tree_n119 (by decide +kernel) (by decide +kernel)
    tree_n088_checked tree_n119_checked

private theorem tree_n086_checked :
    checkDecision fastMetadata false [328, 43, 6, 293, 17, 52, 258] 9 tree_n086 = true := by
  decide +kernel

private theorem tree_n085_checked :
    checkDecision fastMetadata false [257, 44, 43, 6, 293, 17, 52, 258] 9 tree_n085 = true := by
  decide +kernel

private theorem tree_n084_checked :
    checkDecision fastMetadata false [119, 172, 68, 144, 44, 43, 6, 293, 17, 52, 258] 9 tree_n084 = true := by
  decide +kernel

private theorem tree_n083_checked :
    checkDecision fastMetadata false [232, 172, 68, 144, 44, 43, 6, 293, 17, 52, 258] 9 tree_n083 = true := by
  decide +kernel

private theorem tree_n082_checked :
    checkDecision fastMetadata false [172, 68, 144, 44, 43, 6, 293, 17, 52, 258] 9 tree_n082 = true := by
  refine checkDecision_tree_transport fastMetadata false [172, 68, 144, 44, 43, 6, 293, 17, 52, 258] 9
    (.cut 232 tree_n083 tree_n084) tree_n082 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [172, 68, 144, 44, 43, 6, 293, 17, 52, 258] 9 232 119
    tree_n083 tree_n084 (by decide +kernel) (by decide +kernel)
    tree_n083_checked tree_n084_checked

private theorem tree_n081_checked :
    checkDecision fastMetadata false [70, 59, 68, 144, 44, 43, 6, 293, 17, 52, 258] 9 tree_n081 = true := by
  decide +kernel

private theorem tree_n080_checked :
    checkDecision fastMetadata false [183, 59, 68, 144, 44, 43, 6, 293, 17, 52, 258] 9 tree_n080 = true := by
  decide +kernel

private theorem tree_n079_checked :
    checkDecision fastMetadata false [59, 68, 144, 44, 43, 6, 293, 17, 52, 258] 9 tree_n079 = true := by
  refine checkDecision_tree_transport fastMetadata false [59, 68, 144, 44, 43, 6, 293, 17, 52, 258] 9
    (.cut 183 tree_n080 tree_n081) tree_n079 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [59, 68, 144, 44, 43, 6, 293, 17, 52, 258] 9 183 70
    tree_n080 tree_n081 (by decide +kernel) (by decide +kernel)
    tree_n080_checked tree_n081_checked

private theorem tree_n078_checked :
    checkDecision fastMetadata false [68, 144, 44, 43, 6, 293, 17, 52, 258] 9 tree_n078 = true := by
  refine checkDecision_tree_transport fastMetadata false [68, 144, 44, 43, 6, 293, 17, 52, 258] 9
    (.cut 59 tree_n079 tree_n082) tree_n078 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [68, 144, 44, 43, 6, 293, 17, 52, 258] 9 59 172
    tree_n079 tree_n082 (by decide +kernel) (by decide +kernel)
    tree_n079_checked tree_n082_checked

private theorem tree_n077_checked :
    checkDecision fastMetadata false [292, 109, 77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 19 tree_n077 = true := by
  decide +kernel

private theorem tree_n076_checked :
    checkDecision fastMetadata false [292, 109, 77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 15 tree_n076 = true := by
  decide +kernel

private theorem tree_n075_checked :
    checkDecision fastMetadata false [292, 109, 77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 7 tree_n075 = true := by
  decide +kernel

private theorem tree_n074_checked :
    checkDecision fastMetadata false [292, 109, 77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 8 tree_n074 = true := by
  refine checkDecision_tree_transport fastMetadata false [292, 109, 77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 8
    (.split true tree_n075 tree_n076) tree_n074 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [292, 109, 77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 8 7 15
    true tree_n075 tree_n076 (by decide +kernel) (by decide +kernel)
    tree_n075_checked tree_n076_checked

private theorem tree_n073_checked :
    checkDecision fastMetadata false [292, 109, 77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9 tree_n073 = true := by
  refine checkDecision_tree_transport fastMetadata false [292, 109, 77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9
    (.split true tree_n074 tree_n077) tree_n073 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [292, 109, 77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9 8 19
    true tree_n074 tree_n077 (by decide +kernel) (by decide +kernel)
    tree_n074_checked tree_n077_checked

private theorem tree_n072_checked :
    checkDecision fastMetadata false [7, 109, 77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9 tree_n072 = true := by
  decide +kernel

private theorem tree_n071_checked :
    checkDecision fastMetadata false [109, 77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9 tree_n071 = true := by
  refine checkDecision_tree_transport fastMetadata false [109, 77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9
    (.cut 7 tree_n072 tree_n073) tree_n071 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [109, 77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9 7 292
    tree_n072 tree_n073 (by decide +kernel) (by decide +kernel)
    tree_n072_checked tree_n073_checked

private theorem tree_n070_checked :
    checkDecision fastMetadata false [119, 222, 77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 19 tree_n070 = true := by
  decide +kernel

private theorem tree_n069_checked :
    checkDecision fastMetadata false [119, 222, 77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 8 tree_n069 = true := by
  decide +kernel

private theorem tree_n068_checked :
    checkDecision fastMetadata false [119, 222, 77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9 tree_n068 = true := by
  refine checkDecision_tree_transport fastMetadata false [119, 222, 77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9
    (.split true tree_n069 tree_n070) tree_n068 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [119, 222, 77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9 8 19
    true tree_n069 tree_n070 (by decide +kernel) (by decide +kernel)
    tree_n069_checked tree_n070_checked

private theorem tree_n067_checked :
    checkDecision fastMetadata false [232, 222, 77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9 tree_n067 = true := by
  decide +kernel

private theorem tree_n066_checked :
    checkDecision fastMetadata false [222, 77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9 tree_n066 = true := by
  refine checkDecision_tree_transport fastMetadata false [222, 77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9
    (.cut 232 tree_n067 tree_n068) tree_n066 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [222, 77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9 232 119
    tree_n067 tree_n068 (by decide +kernel) (by decide +kernel)
    tree_n067_checked tree_n068_checked

private theorem tree_n065_checked :
    checkDecision fastMetadata false [77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9 tree_n065 = true := by
  refine checkDecision_tree_transport fastMetadata false [77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9
    (.cut 222 tree_n066 tree_n071) tree_n065 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [77, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9 222 109
    tree_n066 tree_n071 (by decide +kernel) (by decide +kernel)
    tree_n066_checked tree_n071_checked

private theorem tree_n064_checked :
    checkDecision fastMetadata false [109, 190, 181, 144, 44, 43, 6, 293, 17, 52, 258] 19 tree_n064 = true := by
  decide +kernel

private theorem tree_n063_checked :
    checkDecision fastMetadata false [109, 190, 181, 144, 44, 43, 6, 293, 17, 52, 258] 15 tree_n063 = true := by
  decide +kernel

private theorem tree_n062_checked :
    checkDecision fastMetadata false [109, 190, 181, 144, 44, 43, 6, 293, 17, 52, 258] 7 tree_n062 = true := by
  decide +kernel

private theorem tree_n061_checked :
    checkDecision fastMetadata false [109, 190, 181, 144, 44, 43, 6, 293, 17, 52, 258] 8 tree_n061 = true := by
  refine checkDecision_tree_transport fastMetadata false [109, 190, 181, 144, 44, 43, 6, 293, 17, 52, 258] 8
    (.split true tree_n062 tree_n063) tree_n061 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [109, 190, 181, 144, 44, 43, 6, 293, 17, 52, 258] 8 7 15
    true tree_n062 tree_n063 (by decide +kernel) (by decide +kernel)
    tree_n062_checked tree_n063_checked

private theorem tree_n060_checked :
    checkDecision fastMetadata false [109, 190, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9 tree_n060 = true := by
  refine checkDecision_tree_transport fastMetadata false [109, 190, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9
    (.split true tree_n061 tree_n064) tree_n060 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [109, 190, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9 8 19
    true tree_n061 tree_n064 (by decide +kernel) (by decide +kernel)
    tree_n061_checked tree_n064_checked

private theorem tree_n059_checked :
    checkDecision fastMetadata false [222, 190, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9 tree_n059 = true := by
  decide +kernel

private theorem tree_n058_checked :
    checkDecision fastMetadata false [190, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9 tree_n058 = true := by
  refine checkDecision_tree_transport fastMetadata false [190, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9
    (.cut 222 tree_n059 tree_n060) tree_n058 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [190, 181, 144, 44, 43, 6, 293, 17, 52, 258] 9 222 109
    tree_n059 tree_n060 (by decide +kernel) (by decide +kernel)
    tree_n059_checked tree_n060_checked

private theorem tree_n057_checked :
    checkDecision fastMetadata false [181, 144, 44, 43, 6, 293, 17, 52, 258] 9 tree_n057 = true := by
  refine checkDecision_tree_transport fastMetadata false [181, 144, 44, 43, 6, 293, 17, 52, 258] 9
    (.cut 190 tree_n058 tree_n065) tree_n057 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [181, 144, 44, 43, 6, 293, 17, 52, 258] 9 190 77
    tree_n058 tree_n065 (by decide +kernel) (by decide +kernel)
    tree_n058_checked tree_n065_checked

private theorem tree_n056_checked :
    checkDecision fastMetadata false [144, 44, 43, 6, 293, 17, 52, 258] 9 tree_n056 = true := by
  refine checkDecision_tree_transport fastMetadata false [144, 44, 43, 6, 293, 17, 52, 258] 9
    (.cut 181 tree_n057 tree_n078) tree_n056 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [144, 44, 43, 6, 293, 17, 52, 258] 9 181 68
    tree_n057 tree_n078 (by decide +kernel) (by decide +kernel)
    tree_n057_checked tree_n078_checked

private theorem tree_n055_checked :
    checkDecision fastMetadata false [44, 43, 6, 293, 17, 52, 258] 9 tree_n055 = true := by
  refine checkDecision_tree_transport fastMetadata false [44, 43, 6, 293, 17, 52, 258] 9
    (.cut 144 tree_n056 tree_n085) tree_n055 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [44, 43, 6, 293, 17, 52, 258] 9 144 257
    tree_n056 tree_n085 (by decide +kernel) (by decide +kernel)
    tree_n056_checked tree_n085_checked

private theorem tree_n054_checked :
    checkDecision fastMetadata false [43, 6, 293, 17, 52, 258] 9 tree_n054 = true := by
  refine checkDecision_tree_transport fastMetadata false [43, 6, 293, 17, 52, 258] 9
    (.cut 44 tree_n055 tree_n086) tree_n054 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [43, 6, 293, 17, 52, 258] 9 44 328
    tree_n055 tree_n086 (by decide +kernel) (by decide +kernel)
    tree_n055_checked tree_n086_checked

private theorem tree_n053_checked :
    checkDecision fastMetadata false [6, 293, 17, 52, 258] 9 tree_n053 = true := by
  refine checkDecision_tree_transport fastMetadata false [6, 293, 17, 52, 258] 9
    (.cut 43 tree_n054 tree_n087) tree_n053 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [6, 293, 17, 52, 258] 9 43 327
    tree_n054 tree_n087 (by decide +kernel) (by decide +kernel)
    tree_n054_checked tree_n087_checked

private theorem tree_n052_checked :
    checkDecision fastMetadata false [293, 17, 52, 258] 9 tree_n052 = true := by
  refine checkDecision_tree_transport fastMetadata false [293, 17, 52, 258] 9
    (.cut 6 tree_n053 tree_n126) tree_n052 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [293, 17, 52, 258] 9 6 291
    tree_n053 tree_n126 (by decide +kernel) (by decide +kernel)
    tree_n053_checked tree_n126_checked

private theorem tree_n051_checked :
    checkDecision fastMetadata false [327, 296, 8, 17, 52, 258] 9 tree_n051 = true := by
  decide +kernel

private theorem tree_n050_checked :
    checkDecision fastMetadata false [124, 70, 43, 296, 8, 17, 52, 258] 9 tree_n050 = true := by
  decide +kernel

private theorem tree_n049_checked :
    checkDecision fastMetadata false [237, 70, 43, 296, 8, 17, 52, 258] 9 tree_n049 = true := by
  decide +kernel

private theorem tree_n048_checked :
    checkDecision fastMetadata false [70, 43, 296, 8, 17, 52, 258] 9 tree_n048 = true := by
  refine checkDecision_tree_transport fastMetadata false [70, 43, 296, 8, 17, 52, 258] 9
    (.cut 237 tree_n049 tree_n050) tree_n048 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [70, 43, 296, 8, 17, 52, 258] 9 237 124
    tree_n049 tree_n050 (by decide +kernel) (by decide +kernel)
    tree_n049_checked tree_n050_checked

private theorem tree_n047_checked :
    checkDecision fastMetadata false [124, 183, 43, 296, 8, 17, 52, 258] 9 tree_n047 = true := by
  decide +kernel

private theorem tree_n046_checked :
    checkDecision fastMetadata false [237, 183, 43, 296, 8, 17, 52, 258] 9 tree_n046 = true := by
  decide +kernel

private theorem tree_n045_checked :
    checkDecision fastMetadata false [183, 43, 296, 8, 17, 52, 258] 9 tree_n045 = true := by
  refine checkDecision_tree_transport fastMetadata false [183, 43, 296, 8, 17, 52, 258] 9
    (.cut 237 tree_n046 tree_n047) tree_n045 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [183, 43, 296, 8, 17, 52, 258] 9 237 124
    tree_n046 tree_n047 (by decide +kernel) (by decide +kernel)
    tree_n046_checked tree_n047_checked

private theorem tree_n044_checked :
    checkDecision fastMetadata false [43, 296, 8, 17, 52, 258] 9 tree_n044 = true := by
  refine checkDecision_tree_transport fastMetadata false [43, 296, 8, 17, 52, 258] 9
    (.cut 183 tree_n045 tree_n048) tree_n044 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [43, 296, 8, 17, 52, 258] 9 183 70
    tree_n045 tree_n048 (by decide +kernel) (by decide +kernel)
    tree_n045_checked tree_n048_checked

private theorem tree_n043_checked :
    checkDecision fastMetadata false [296, 8, 17, 52, 258] 9 tree_n043 = true := by
  refine checkDecision_tree_transport fastMetadata false [296, 8, 17, 52, 258] 9
    (.cut 43 tree_n044 tree_n051) tree_n043 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [296, 8, 17, 52, 258] 9 43 327
    tree_n044 tree_n051 (by decide +kernel) (by decide +kernel)
    tree_n044_checked tree_n051_checked

private theorem tree_n042_checked :
    checkDecision fastMetadata false [250, 11, 8, 17, 52, 258] 9 tree_n042 = true := by
  decide +kernel

private theorem tree_n041_checked :
    checkDecision fastMetadata false [299, 137, 11, 8, 17, 52, 258] 9 tree_n041 = true := by
  decide +kernel

private theorem tree_n040_checked :
    checkDecision fastMetadata false [265, 93, 263, 14, 137, 11, 8, 17, 52, 258] 9 tree_n040 = true := by
  decide +kernel

private theorem tree_n039_checked :
    checkDecision fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 32 tree_n039 = true := by
  decide +kernel

private theorem tree_n038_checked :
    checkDecision fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 25 tree_n038 = true := by
  decide +kernel

private theorem tree_n037_checked :
    checkDecision fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 31 tree_n037 = true := by
  refine checkDecision_tree_transport fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 31
    (.split false tree_n038 tree_n039) tree_n037 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 31 25 32
    false tree_n038 tree_n039 (by decide +kernel) (by decide +kernel)
    tree_n038_checked tree_n039_checked

private theorem tree_n036_checked :
    checkDecision fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 29 tree_n036 = true := by
  decide +kernel

private theorem tree_n035_checked :
    checkDecision fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 30 tree_n035 = true := by
  refine checkDecision_tree_transport fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 30
    (.split true tree_n036 tree_n037) tree_n035 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 30 29 31
    true tree_n036 tree_n037 (by decide +kernel) (by decide +kernel)
    tree_n036_checked tree_n037_checked

private theorem tree_n034_checked :
    checkDecision fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 3 tree_n034 = true := by
  decide +kernel

private theorem tree_n033_checked :
    checkDecision fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 24 tree_n033 = true := by
  refine checkDecision_tree_transport fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 24
    (.split false tree_n034 tree_n035) tree_n033 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 24 3 30
    false tree_n034 tree_n035 (by decide +kernel) (by decide +kernel)
    tree_n034_checked tree_n035_checked

private theorem tree_n032_checked :
    checkDecision fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 22 tree_n032 = true := by
  decide +kernel

private theorem tree_n031_checked :
    checkDecision fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 23 tree_n031 = true := by
  refine checkDecision_tree_transport fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 23
    (.split true tree_n032 tree_n033) tree_n031 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 23 22 24
    true tree_n032 tree_n033 (by decide +kernel) (by decide +kernel)
    tree_n032_checked tree_n033_checked

private theorem tree_n030_checked :
    checkDecision fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 20 tree_n030 = true := by
  decide +kernel

private theorem tree_n029_checked :
    checkDecision fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 21 tree_n029 = true := by
  refine checkDecision_tree_transport fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 21
    (.split true tree_n030 tree_n031) tree_n029 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 21 20 23
    true tree_n030 tree_n031 (by decide +kernel) (by decide +kernel)
    tree_n030_checked tree_n031_checked

private theorem tree_n028_checked :
    checkDecision fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 18 tree_n028 = true := by
  decide +kernel

private theorem tree_n027_checked :
    checkDecision fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 19 tree_n027 = true := by
  refine checkDecision_tree_transport fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 19
    (.split true tree_n028 tree_n029) tree_n027 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 19 18 21
    true tree_n028 tree_n029 (by decide +kernel) (by decide +kernel)
    tree_n028_checked tree_n029_checked

private theorem tree_n026_checked :
    checkDecision fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 8 tree_n026 = true := by
  decide +kernel

private theorem tree_n025_checked :
    checkDecision fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 9 tree_n025 = true := by
  refine checkDecision_tree_transport fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 9
    (.split true tree_n026 tree_n027) tree_n025 (by rfl) ?_
  exact checkDecision_split_of fastMetadata false [145, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 9 8 19
    true tree_n026 tree_n027 (by decide +kernel) (by decide +kernel)
    tree_n026_checked tree_n027_checked

private theorem tree_n024_checked :
    checkDecision fastMetadata false [259, 151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 9 tree_n024 = true := by
  decide +kernel

private theorem tree_n023_checked :
    checkDecision fastMetadata false [151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 9 tree_n023 = true := by
  refine checkDecision_tree_transport fastMetadata false [151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 9
    (.cut 259 tree_n024 tree_n025) tree_n023 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [151, 93, 263, 14, 137, 11, 8, 17, 52, 258] 9 259 145
    tree_n024 tree_n025 (by decide +kernel) (by decide +kernel)
    tree_n024_checked tree_n025_checked

private theorem tree_n022_checked :
    checkDecision fastMetadata false [93, 263, 14, 137, 11, 8, 17, 52, 258] 9 tree_n022 = true := by
  refine checkDecision_tree_transport fastMetadata false [93, 263, 14, 137, 11, 8, 17, 52, 258] 9
    (.cut 151 tree_n023 tree_n040) tree_n022 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [93, 263, 14, 137, 11, 8, 17, 52, 258] 9 151 265
    tree_n023 tree_n040 (by decide +kernel) (by decide +kernel)
    tree_n023_checked tree_n040_checked

private theorem tree_n021_checked :
    checkDecision fastMetadata false [81, 151, 206, 263, 14, 137, 11, 8, 17, 52, 258] 9 tree_n021 = true := by
  decide +kernel

private theorem tree_n020_checked :
    checkDecision fastMetadata false [194, 151, 206, 263, 14, 137, 11, 8, 17, 52, 258] 9 tree_n020 = true := by
  decide +kernel

private theorem tree_n019_checked :
    checkDecision fastMetadata false [151, 206, 263, 14, 137, 11, 8, 17, 52, 258] 9 tree_n019 = true := by
  refine checkDecision_tree_transport fastMetadata false [151, 206, 263, 14, 137, 11, 8, 17, 52, 258] 9
    (.cut 194 tree_n020 tree_n021) tree_n019 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [151, 206, 263, 14, 137, 11, 8, 17, 52, 258] 9 194 81
    tree_n020 tree_n021 (by decide +kernel) (by decide +kernel)
    tree_n020_checked tree_n021_checked

private theorem tree_n018_checked :
    checkDecision fastMetadata false [265, 206, 263, 14, 137, 11, 8, 17, 52, 258] 9 tree_n018 = true := by
  decide +kernel

private theorem tree_n017_checked :
    checkDecision fastMetadata false [206, 263, 14, 137, 11, 8, 17, 52, 258] 9 tree_n017 = true := by
  refine checkDecision_tree_transport fastMetadata false [206, 263, 14, 137, 11, 8, 17, 52, 258] 9
    (.cut 265 tree_n018 tree_n019) tree_n017 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [206, 263, 14, 137, 11, 8, 17, 52, 258] 9 265 151
    tree_n018 tree_n019 (by decide +kernel) (by decide +kernel)
    tree_n018_checked tree_n019_checked

private theorem tree_n016_checked :
    checkDecision fastMetadata false [263, 14, 137, 11, 8, 17, 52, 258] 9 tree_n016 = true := by
  refine checkDecision_tree_transport fastMetadata false [263, 14, 137, 11, 8, 17, 52, 258] 9
    (.cut 206 tree_n017 tree_n022) tree_n016 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [263, 14, 137, 11, 8, 17, 52, 258] 9 206 93
    tree_n017 tree_n022 (by decide +kernel) (by decide +kernel)
    tree_n017_checked tree_n022_checked

private theorem tree_n015_checked :
    checkDecision fastMetadata false [259, 89, 81, 297, 149, 14, 137, 11, 8, 17, 52, 258] 9 tree_n015 = true := by
  decide +kernel

private theorem tree_n014_checked :
    checkDecision fastMetadata false [145, 89, 81, 297, 149, 14, 137, 11, 8, 17, 52, 258] 9 tree_n014 = true := by
  decide +kernel

private theorem tree_n013_checked :
    checkDecision fastMetadata false [89, 81, 297, 149, 14, 137, 11, 8, 17, 52, 258] 9 tree_n013 = true := by
  refine checkDecision_tree_transport fastMetadata false [89, 81, 297, 149, 14, 137, 11, 8, 17, 52, 258] 9
    (.cut 145 tree_n014 tree_n015) tree_n013 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [89, 81, 297, 149, 14, 137, 11, 8, 17, 52, 258] 9 145 259
    tree_n014 tree_n015 (by decide +kernel) (by decide +kernel)
    tree_n014_checked tree_n015_checked

private theorem tree_n012_checked :
    checkDecision fastMetadata false [202, 81, 297, 149, 14, 137, 11, 8, 17, 52, 258] 9 tree_n012 = true := by
  decide +kernel

private theorem tree_n011_checked :
    checkDecision fastMetadata false [81, 297, 149, 14, 137, 11, 8, 17, 52, 258] 9 tree_n011 = true := by
  refine checkDecision_tree_transport fastMetadata false [81, 297, 149, 14, 137, 11, 8, 17, 52, 258] 9
    (.cut 202 tree_n012 tree_n013) tree_n011 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [81, 297, 149, 14, 137, 11, 8, 17, 52, 258] 9 202 89
    tree_n012 tree_n013 (by decide +kernel) (by decide +kernel)
    tree_n012_checked tree_n013_checked

private theorem tree_n010_checked :
    checkDecision fastMetadata false [194, 297, 149, 14, 137, 11, 8, 17, 52, 258] 9 tree_n010 = true := by
  decide +kernel

private theorem tree_n009_checked :
    checkDecision fastMetadata false [297, 149, 14, 137, 11, 8, 17, 52, 258] 9 tree_n009 = true := by
  refine checkDecision_tree_transport fastMetadata false [297, 149, 14, 137, 11, 8, 17, 52, 258] 9
    (.cut 194 tree_n010 tree_n011) tree_n009 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [297, 149, 14, 137, 11, 8, 17, 52, 258] 9 194 81
    tree_n010 tree_n011 (by decide +kernel) (by decide +kernel)
    tree_n010_checked tree_n011_checked

private theorem tree_n008_checked :
    checkDecision fastMetadata false [145, 12, 149, 14, 137, 11, 8, 17, 52, 258] 9 tree_n008 = true := by
  decide +kernel

private theorem tree_n007_checked :
    checkDecision fastMetadata false [259, 12, 149, 14, 137, 11, 8, 17, 52, 258] 9 tree_n007 = true := by
  decide +kernel

private theorem tree_n006_checked :
    checkDecision fastMetadata false [12, 149, 14, 137, 11, 8, 17, 52, 258] 9 tree_n006 = true := by
  refine checkDecision_tree_transport fastMetadata false [12, 149, 14, 137, 11, 8, 17, 52, 258] 9
    (.cut 259 tree_n007 tree_n008) tree_n006 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [12, 149, 14, 137, 11, 8, 17, 52, 258] 9 259 145
    tree_n007 tree_n008 (by decide +kernel) (by decide +kernel)
    tree_n007_checked tree_n008_checked

private theorem tree_n005_checked :
    checkDecision fastMetadata false [149, 14, 137, 11, 8, 17, 52, 258] 9 tree_n005 = true := by
  refine checkDecision_tree_transport fastMetadata false [149, 14, 137, 11, 8, 17, 52, 258] 9
    (.cut 12 tree_n006 tree_n009) tree_n005 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [149, 14, 137, 11, 8, 17, 52, 258] 9 12 297
    tree_n006 tree_n009 (by decide +kernel) (by decide +kernel)
    tree_n006_checked tree_n009_checked

private theorem tree_n004_checked :
    checkDecision fastMetadata false [14, 137, 11, 8, 17, 52, 258] 9 tree_n004 = true := by
  refine checkDecision_tree_transport fastMetadata false [14, 137, 11, 8, 17, 52, 258] 9
    (.cut 149 tree_n005 tree_n016) tree_n004 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [14, 137, 11, 8, 17, 52, 258] 9 149 263
    tree_n005 tree_n016 (by decide +kernel) (by decide +kernel)
    tree_n005_checked tree_n016_checked

private theorem tree_n003_checked :
    checkDecision fastMetadata false [137, 11, 8, 17, 52, 258] 9 tree_n003 = true := by
  refine checkDecision_tree_transport fastMetadata false [137, 11, 8, 17, 52, 258] 9
    (.cut 14 tree_n004 tree_n041) tree_n003 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [137, 11, 8, 17, 52, 258] 9 14 299
    tree_n004 tree_n041 (by decide +kernel) (by decide +kernel)
    tree_n004_checked tree_n041_checked

private theorem tree_n002_checked :
    checkDecision fastMetadata false [11, 8, 17, 52, 258] 9 tree_n002 = true := by
  refine checkDecision_tree_transport fastMetadata false [11, 8, 17, 52, 258] 9
    (.cut 137 tree_n003 tree_n042) tree_n002 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [11, 8, 17, 52, 258] 9 137 250
    tree_n003 tree_n042 (by decide +kernel) (by decide +kernel)
    tree_n003_checked tree_n042_checked

private theorem tree_n001_checked :
    checkDecision fastMetadata false [8, 17, 52, 258] 9 tree_n001 = true := by
  refine checkDecision_tree_transport fastMetadata false [8, 17, 52, 258] 9
    (.cut 11 tree_n002 tree_n043) tree_n001 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [8, 17, 52, 258] 9 11 296
    tree_n002 tree_n043 (by decide +kernel) (by decide +kernel)
    tree_n002_checked tree_n043_checked

private theorem tree_n000_checked :
    checkDecision fastMetadata false [17, 52, 258] 9 tree_n000 = true := by
  refine checkDecision_tree_transport fastMetadata false [17, 52, 258] 9
    (.cut 8 tree_n001 tree_n052) tree_n000 (by rfl) ?_
  exact checkDecision_cut_of fastMetadata false [17, 52, 258] 9 8 293
    tree_n001 tree_n052 (by decide +kernel) (by decide +kernel)
    tree_n001_checked tree_n052_checked

private theorem other_check_fast :
    checkDecision fastMetadata false [17, 52, 258] 9 (lateTree false) = true := by
  exact checkDecision_tree_transport fastMetadata false [17, 52, 258] 9
    tree_n000 (lateTree false) generated_tree_exact tree_n000_checked

private theorem other_check :
    checkDecision otherMetadata false [17, 52, 258] 9 (lateTree false) = true := by
  exact checkDecision_metadata_transport fastMetadata otherMetadata fastMetadata_eq
    false [17, 52, 258] 9 (lateTree false) other_check_fast

end DiscoveryFreimanOtherReflection

open DiscoveryFreimanOtherReflection in
theorem solution :
    Freiman.lateDecisionValid Freiman.lateCatalog false Freiman.lateRootBounds
      (Freiman.lateRootRectangle false) (Freiman.lateTree false) := by
  exact checkDecision_at_root lateCatalog otherMetadata other_faithful false
    [17, 52, 258] 9 (lateRootRectangle false) (lateTree false)
    other_root_rectangle other_check

private def expectedTargetType : Prop :=
  Freiman.lateDecisionValid Freiman.lateCatalog false Freiman.lateRootBounds
    (Freiman.lateRootRectangle false) (Freiman.lateTree false)

example : expectedTargetType := solution

#print axioms solution
