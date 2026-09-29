-- Prove2me | solution 1 for Freiman.late_decision_right3_valid
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T08:15:06.454125+00:00
-- url     : https://prove2.me/submissions/94a16221-dbf2-47e1-bb4f-dac40f066358

import Definitions.Def_Freiman_lateData
import Mathlib.Data.Finset.Dedup

/-! Structural validity of the public right3 decision tree via exact catalog metadata. -/

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option Elab.async false
open Freiman
namespace DiscoveryFreimanReflectedMetadata


private structure WitnessKey where
  lower : ℕ
  upper : ℕ
  rectangle : ℕ

private structure PathKey where
  right3 : Bool
  incoming : List ℕ
  required : List ℕ
  implications : List (ℕ × Option ℕ)

/-- Partial lookups permit retaining only the source rows actually consumed.
Counts are the sizes of the original public arrays, not the partial tables. -/
private structure IndexMetadata where
  boundCount : ℕ
  proofCount : ℕ
  witnessCount : ℕ
  pathCount : ℕ
  rectangleId : ℕ
  complement : ℕ → Option ℕ
  pairNode : ℕ → Option ℕ
  witnessKey : ℕ → Option WitnessKey
  pathKey : ℕ → Option PathKey

/-- These obligations concern literal public lookups and projections only.
No field assumes either the public validator or the result of the checker. -/
private structure MetadataFaithful
    (C : LateCatalog) (D : IndexMetadata) (R : CertRectangle) : Prop where
  bound_count : D.boundCount = C.bounds.size
  proof_count : D.proofCount = C.proofs.size
  witness_count : D.witnessCount = C.witnesses.size
  path_count : D.pathCount = C.paths.size
  complement : ∀ i j, D.complement i = some j →
    lowerHistoryComplement (lateBound C i) = lateBound C j
  pair_node : ∀ pid wid, D.pairNode pid = some wid →
    C.proofs[pid - 1]?.getD (.pair 0) = .pair wid
  witness_key : ∀ wid w, D.witnessKey wid = some w →
    (lateWitnessRow C wid).lower = w.lower ∧
    (lateWitnessRow C wid).upper = w.upper ∧
    (lateWitnessRow C wid).rectangle = w.rectangle
  path_key : ∀ pid p, D.pathKey pid = some p →
    (latePath C pid).right3 = p.right3 ∧
    (latePath C pid).incoming = p.incoming ∧
    (latePath C pid).required = p.required ∧
    (latePath C pid).implications = p.implications
  rectangle : lateRectangle C D.rectangleId = R

private def checkPair (D : IndexMetadata) (ids : List ℕ) (pid : ℕ) : Bool :=
  decide (0 < pid ∧ pid ≤ D.proofCount) &&
    match D.pairNode pid with
    | none => false
    | some wid =>
      match D.witnessKey wid with
      | none => false
      | some w => decide (0 < wid ∧ wid ≤ D.witnessCount ∧
          w.lower ∈ ids ∧ w.upper ∈ ids ∧ w.rectangle = D.rectangleId)

private def checkImplication (D : IndexMetadata) (ids : List ℕ)
    (imp : ℕ × Option ℕ) : Bool :=
  match imp.2 with
  | none => decide (imp.1 ∈ ids)
  | some pid =>
    match D.complement imp.1 with
    | none => false
    | some neg => checkPair D (neg :: ids) pid

private def checkPath (D : IndexMetadata) (right3 : Bool)
    (ids : List ℕ) (pid : ℕ) : Bool :=
  match D.pathKey pid with
  | none => false
  | some p =>
    decide (0 < pid ∧ pid ≤ D.pathCount ∧ p.right3 = right3 ∧
      p.incoming.toFinset = ids.toFinset ∧
      (p.implications.map Prod.fst).toFinset = p.required.toFinset) &&
        p.implications.all (checkImplication D ids)

/-- Unsupported constructors fail rather than omit a public obligation. -/
private def checkDecision (D : IndexMetadata) (right3 : Bool) :
    List ℕ → LateDecisionTree → Bool
  | ids, .cut bid left right =>
    decide (0 < bid ∧ bid ≤ D.boundCount) &&
      match D.complement bid with
      | none => false
      | some neg =>
        checkDecision D right3 (bid :: ids) left &&
          checkDecision D right3 (neg :: ids) right
  | ids, .path pid => checkPath D right3 ids pid
  | _, .split _ _ _ => false
  | _, .empty _ => false

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

private theorem checkPair_sound (C : LateCatalog) (D : IndexMetadata)
    (R : CertRectangle) (hD : MetadataFaithful C D R)
    (ids : List ℕ) (pid : ℕ) (h : checkPair D ids pid = true) :
    lateProofValid C 1500 (lateBounds C ids) R pid := by
  unfold checkPair at h
  have hp : 0 < pid ∧ pid ≤ D.proofCount :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
  have hm := (Bool.and_eq_true_iff.mp h).2
  cases hn : D.pairNode pid with
  | none =>
    have hf : false = true := by simpa only [hn] using hm
    cases hf
  | some wid =>
    cases hw : D.witnessKey wid with
    | none =>
      have hf : false = true := by simpa only [hn, hw] using hm
      cases hf
    | some w =>
      have hvalid : 0 < wid ∧ wid ≤ D.witnessCount ∧
          w.lower ∈ ids ∧ w.upper ∈ ids ∧ w.rectangle = D.rectangleId :=
        of_decide_eq_true (by simpa only [hn, hw] using hm)
      rcases hvalid with ⟨hwpos, hwle, hlo, hhi, hrid⟩
      have hpid : lateIndex pid C.proofs.size := by
        rw [← hD.proof_count]
        exact hp
      have hwid : lateIndex wid C.witnesses.size := by
        rw [← hD.witness_count]
        exact ⟨hwpos, hwle⟩
      have hrow := hD.witness_key wid w hw
      change lateIndex pid C.proofs.size ∧ _
      refine ⟨hpid, ?_⟩
      rw [hD.pair_node pid wid hn]
      refine ⟨hwid, ?_, ?_, ?_⟩
      · change lateBound C (lateWitnessRow C wid).lower ∈ lateBounds C ids
        rw [hrow.1]
        exact bounds_mem_of_id C hlo
      · change lateBound C (lateWitnessRow C wid).upper ∈ lateBounds C ids
        rw [hrow.2.1]
        exact bounds_mem_of_id C hhi
      · change lateRectangle C (lateWitnessRow C wid).rectangle = R
        rw [hrow.2.2, hrid]
        exact hD.rectangle

private theorem checkImplication_sound (C : LateCatalog) (D : IndexMetadata)
    (R : CertRectangle) (hD : MetadataFaithful C D R)
    (ids : List ℕ) (imp : ℕ × Option ℕ)
    (h : checkImplication D ids imp = true) :
    match imp.2 with
    | none => lateBound C imp.1 ∈ lateBounds C ids
    | some pid => lateProofValid C 1500
        (lowerHistoryComplement (lateBound C imp.1) :: lateBounds C ids) R pid := by
  rcases imp with ⟨target, choice⟩
  cases choice with
  | none =>
    exact bounds_mem_of_id C (of_decide_eq_true h)
  | some pid =>
    cases hc : D.complement target with
    | none =>
      have hf : false = true := by simpa only [checkImplication, hc] using h
      cases hf
    | some neg =>
      have hp : checkPair D (neg :: ids) pid = true := by
        simpa only [checkImplication, hc] using h
      change lateProofValid C 1500
        (lowerHistoryComplement (lateBound C target) :: lateBounds C ids) R pid
      rw [hD.complement target neg hc]
      exact checkPair_sound C D R hD (neg :: ids) pid hp

private theorem checkPath_sound (C : LateCatalog) (D : IndexMetadata)
    (R : CertRectangle) (hD : MetadataFaithful C D R)
    (right3 : Bool) (ids : List ℕ) (pid : ℕ)
    (h : checkPath D right3 ids pid = true) :
    lateDecisionValid C right3 (lateBounds C ids) R (.path pid) := by
  cases hpath : D.pathKey pid with
  | none =>
    have hf : false = true := by simpa only [checkPath, hpath] using h
    cases hf
  | some p =>
    have hcheck :
        (decide (0 < pid ∧ pid ≤ D.pathCount ∧ p.right3 = right3 ∧
          p.incoming.toFinset = ids.toFinset ∧
          (p.implications.map Prod.fst).toFinset = p.required.toFinset) &&
            p.implications.all (checkImplication D ids)) = true := by
      simpa only [checkPath, hpath] using h
    have hmeta := of_decide_eq_true (Bool.and_eq_true_iff.mp hcheck).1
    have hall := (Bool.and_eq_true_iff.mp hcheck).2
    rcases hmeta with ⟨hp0, hple, hright, hincoming, hcover⟩
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
        exact checkImplication_sound C D R hD ids imp
          (List.all_eq_true.mp hall imp himp)

/-- One source-faithful pure-data check implies the exact public proposition.
The actual public tree can be supplied directly as `tree`; no reconstruction
or tree-equivalence certificate is required. -/
private theorem checkDecision_sound (C : LateCatalog) (D : IndexMetadata)
    (R : CertRectangle) (hD : MetadataFaithful C D R) (right3 : Bool)
    (ids : List ℕ) (tree : LateDecisionTree)
    (h : checkDecision D right3 ids tree = true) :
    lateDecisionValid C right3 (lateBounds C ids) R tree := by
  induction tree generalizing ids with
  | cut bid left right ihleft ihright =>
    have hsplit :
        (decide (0 < bid ∧ bid ≤ D.boundCount) &&
          (match D.complement bid with
          | none => false
          | some neg => checkDecision D right3 (bid :: ids) left &&
              checkDecision D right3 (neg :: ids) right)) = true := h
    have hbid : lateIndex bid C.bounds.size := by
      rw [← hD.bound_count]
      change 0 < bid ∧ bid ≤ D.boundCount
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp hsplit).1
    have hbranches := (Bool.and_eq_true_iff.mp hsplit).2
    cases hc : D.complement bid with
    | none =>
      have hf : false = true := by simpa only [hc] using hbranches
      cases hf
    | some neg =>
      have hb : checkDecision D right3 (bid :: ids) left = true ∧
          checkDecision D right3 (neg :: ids) right = true :=
        Bool.and_eq_true_iff.mp (by simpa only [hc] using hbranches)
      change lateIndex bid C.bounds.size ∧ _
      refine ⟨hbid, ?_, ?_⟩
      · exact ihleft (bid :: ids) hb.1
      · rw [hD.complement bid neg hc]
        exact ihright (neg :: ids) hb.2
  | split axis left right ihleft ihright =>
    have hf : false = true := h
    cases hf
  | empty pid =>
    have hf : false = true := h
    cases hf
  | path pid =>
    exact checkPath_sound C D R hD right3 ids pid h


private theorem bound_list (i : ℕ) : lateBound lateCatalog i =
    lateBoundData.toList[i - 1]?.getD lateZeroBound := by
  change lateBoundData[i - 1]?.getD lateZeroBound = _
  rw [Array.getElem?_toList]

private def complementPairs : List (ℕ × ℕ) :=
  [
    (1, 286),
    (2, 287),
    (3, 288),
    (5, 290),
    (6, 291),
    (7, 292),
    (8, 293),
    (11, 296),
    (12, 297),
    (13, 298),
    (14, 299),
    (20, 304),
    (21, 305),
    (22, 306),
    (26, 310),
    (27, 311),
    (33, 317),
    (35, 319),
    (36, 320),
    (38, 322),
    (40, 324),
    (41, 325),
    (43, 327),
    (44, 328),
    (48, 332),
    (53, 336),
    (59, 172),
    (60, 173),
    (61, 174),
    (62, 175),
    (64, 177),
    (65, 178),
    (66, 179),
    (75, 188),
    (76, 189),
    (83, 196),
    (85, 198),
    (87, 200),
    (91, 204),
    (94, 207),
    (95, 208),
    (97, 210),
    (99, 212),
    (104, 217),
    (105, 218),
    (106, 219),
    (109, 222),
    (110, 223),
    (112, 225),
    (113, 226),
    (114, 227),
    (116, 229),
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
    (149, 263),
    (151, 265),
    (181, 68),
    (183, 70),
    (185, 72),
    (190, 77),
    (193, 80),
    (194, 81),
    (195, 82),
    (202, 89),
    (203, 90),
    (209, 96),
    (213, 100),
    (221, 108),
    (224, 111),
    (231, 118),
    (235, 122),
    (237, 124),
    (238, 125),
    (242, 129),
    (243, 130),
    (247, 134),
    (248, 135),
    (251, 138),
    (252, 139),
    (253, 140),
    (255, 142),
    (259, 145),
    (261, 147),
    (262, 148),
    (263, 149),
    (264, 150),
    (266, 152),
    (267, 153),
    (268, 154),
    (271, 157),
    (272, 158),
    (274, 160),
    (275, 161),
    (277, 163),
    (279, 165),
    (280, 166),
    (281, 167),
    (282, 168),
    (283, 169),
    (284, 170),
    (285, 171),
    (300, 15),
    (301, 16),
    (313, 29),
    (315, 31),
    (316, 32),
    (323, 39),
    (327, 43),
    (328, 44),
    (329, 45),
    (330, 46),
    (331, 47),
    (333, 49),
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

private theorem proof_suffix : lateProofData.toList.drop 1090 =
    (List.range' 1070 404).map LateProofNode.pair := by rfl

private theorem proof_suffix_lookup (k : ℕ) (hk : k < 404) :
    lateCatalog.proofs[1090 + k]?.getD (.pair 0) = .pair (1070 + k) := by
  change lateProofData[1090 + k]?.getD (.pair 0) = _
  rw [← Array.getElem?_toList, ← List.getElem?_drop, proof_suffix,
    List.getElem?_map, List.getElem?_range' hk]
  simp only [Nat.one_mul, Option.map_some, Option.getD_some]

private def lookupPair (pid : ℕ) : Option ℕ :=
  if 1091 ≤ pid ∧ pid ≤ 1494 then some (1070 + (pid - 1091)) else none

private theorem lookupPair_faithful (pid wid : ℕ)
    (h : lookupPair pid = some wid) :
    lateCatalog.proofs[pid - 1]?.getD (.pair 0) = .pair wid := by
  unfold lookupPair at h
  split at h
  next hrange =>
    have he : 1070 + (pid - 1091) = wid := Option.some.inj h
    have hk : pid - 1091 < 404 := by omega
    have hi : pid - 1 = 1090 + (pid - 1091) := by omega
    rw [hi, ← he]
    exact proof_suffix_lookup (pid - 1091) hk
  next => contradiction

private abbrev WKey := ℕ × ℕ × ℕ
private abbrev PKey := Bool × List ℕ × List ℕ × List (ℕ × Option ℕ)

private def witnessKeys : List WKey :=
  [
    (12, 286, 6),
    (12, 287, 6),
    (12, 298, 6),
    (12, 324, 6),
    (12, 327, 6),
    (12, 328, 6),
    (12, 172, 6),
    (12, 174, 6),
    (12, 177, 6),
    (12, 200, 6),
    (12, 204, 6),
    (12, 210, 6),
    (12, 217, 6),
    (12, 218, 6),
    (12, 219, 6),
    (12, 225, 6),
    (12, 229, 6),
    (12, 236, 6),
    (12, 240, 6),
    (12, 244, 6),
    (12, 250, 6),
    (12, 254, 6),
    (12, 257, 6),
    (12, 265, 6),
    (90, 258, 6),
    (100, 258, 6),
    (111, 258, 6),
    (122, 258, 6),
    (130, 258, 6),
    (145, 258, 6),
    (147, 258, 6),
    (150, 258, 6),
    (152, 258, 6),
    (154, 258, 6),
    (157, 258, 6),
    (158, 258, 6),
    (160, 258, 6),
    (161, 258, 6),
    (167, 258, 6),
    (169, 258, 6),
    (170, 258, 6),
    (15, 258, 6),
    (29, 258, 6),
    (32, 258, 6),
    (45, 258, 6),
    (49, 258, 6),
    (51, 258, 6),
    (54, 258, 6),
    (56, 258, 6),
    (58, 258, 6),
    (149, 286, 6),
    (149, 288, 6),
    (149, 298, 6),
    (149, 311, 6),
    (149, 327, 6),
    (149, 328, 6),
    (149, 172, 6),
    (149, 174, 6),
    (149, 200, 6),
    (149, 210, 6),
    (149, 219, 6),
    (149, 240, 6),
    (149, 244, 6),
    (149, 250, 6),
    (149, 254, 6),
    (149, 257, 6),
    (111, 297, 6),
    (122, 297, 6),
    (130, 297, 6),
    (139, 297, 6),
    (145, 194, 6),
    (150, 297, 6),
    (152, 297, 6),
    (157, 297, 6),
    (158, 297, 6),
    (161, 297, 6),
    (163, 297, 6),
    (166, 297, 6),
    (169, 297, 6),
    (170, 297, 6),
    (171, 297, 6),
    (15, 297, 6),
    (29, 297, 6),
    (39, 297, 6),
    (54, 297, 6),
    (56, 297, 6),
    (81, 286, 6),
    (81, 287, 6),
    (81, 288, 6),
    (81, 298, 6),
    (81, 319, 6),
    (81, 327, 6),
    (81, 328, 6),
    (81, 172, 6),
    (81, 174, 6),
    (81, 177, 6),
    (81, 200, 6),
    (81, 204, 6),
    (81, 210, 6),
    (81, 217, 6),
    (81, 218, 6),
    (81, 219, 6),
    (81, 225, 6),
    (81, 229, 6),
    (81, 240, 6),
    (81, 244, 6),
    (81, 250, 6),
    (81, 254, 6),
    (81, 257, 6),
    (81, 265, 6),
    (89, 297, 6),
    (145, 297, 6),
    (147, 297, 6),
    (160, 297, 6),
    (14, 286, 6),
    (14, 298, 6),
    (14, 310, 6),
    (14, 311, 6),
    (14, 327, 6),
    (14, 328, 6),
    (14, 336, 6),
    (14, 172, 6),
    (14, 174, 6),
    (14, 179, 6),
    (14, 188, 6),
    (14, 200, 6),
    (14, 208, 6),
    (14, 210, 6),
    (14, 212, 6),
    (14, 219, 6),
    (14, 240, 6),
    (14, 244, 6),
    (14, 250, 6),
    (14, 254, 6),
    (14, 256, 6),
    (14, 257, 6),
    (81, 263, 6),
    (111, 263, 6),
    (122, 263, 6),
    (130, 263, 6),
    (145, 263, 6),
    (150, 263, 6),
    (152, 263, 6),
    (157, 263, 6),
    (158, 263, 6),
    (161, 263, 6),
    (163, 263, 6),
    (169, 263, 6),
    (170, 263, 6),
    (15, 263, 6),
    (29, 263, 6),
    (54, 263, 6),
    (56, 263, 6),
    (11, 286, 6),
    (11, 306, 6),
    (11, 310, 6),
    (11, 327, 6),
    (11, 328, 6),
    (11, 336, 6),
    (11, 172, 6),
    (11, 174, 6),
    (11, 175, 6),
    (11, 179, 6),
    (11, 188, 6),
    (11, 189, 6),
    (11, 200, 6),
    (11, 208, 6),
    (11, 210, 6),
    (11, 212, 6),
    (11, 219, 6),
    (11, 227, 6),
    (11, 244, 6),
    (11, 254, 6),
    (11, 256, 6),
    (11, 257, 6),
    (96, 185, 6),
    (111, 185, 6),
    (122, 185, 6),
    (135, 185, 6),
    (145, 185, 6),
    (149, 185, 6),
    (150, 185, 6),
    (158, 185, 6),
    (163, 185, 6),
    (170, 185, 6),
    (15, 185, 6),
    (46, 185, 6),
    (54, 185, 6),
    (72, 286, 6),
    (72, 298, 6),
    (72, 310, 6),
    (72, 311, 6),
    (72, 327, 6),
    (72, 328, 6),
    (72, 336, 6),
    (72, 172, 6),
    (72, 174, 6),
    (72, 175, 6),
    (72, 179, 6),
    (72, 188, 6),
    (72, 189, 6),
    (72, 200, 6),
    (72, 208, 6),
    (72, 210, 6),
    (72, 212, 6),
    (72, 219, 6),
    (72, 227, 6),
    (72, 240, 6),
    (72, 244, 6),
    (72, 250, 6),
    (72, 254, 6),
    (72, 256, 6),
    (72, 257, 6),
    (81, 299, 6),
    (96, 299, 6),
    (111, 299, 6),
    (122, 299, 6),
    (130, 299, 6),
    (135, 299, 6),
    (145, 299, 6),
    (149, 299, 6),
    (150, 299, 6),
    (152, 299, 6),
    (157, 299, 6),
    (158, 299, 6),
    (161, 299, 6),
    (163, 299, 6),
    (169, 299, 6),
    (170, 299, 6),
    (15, 299, 6),
    (29, 299, 6),
    (46, 299, 6),
    (54, 299, 6),
    (56, 299, 6),
    (43, 305, 6),
    (8, 310, 6),
    (43, 328, 6),
    (8, 332, 6),
    (43, 336, 6),
    (8, 172, 6),
    (43, 174, 6),
    (43, 175, 6),
    (43, 179, 6),
    (43, 188, 6),
    (43, 189, 6),
    (43, 200, 6),
    (43, 208, 6),
    (43, 210, 6),
    (43, 212, 6),
    (8, 227, 6),
    (8, 234, 6),
    (8, 239, 6),
    (8, 254, 6),
    (43, 256, 6),
    (8, 257, 6),
    (70, 296, 6),
    (96, 296, 6),
    (122, 296, 6),
    (125, 296, 6),
    (129, 296, 6),
    (135, 296, 6),
    (138, 296, 6),
    (142, 296, 6),
    (145, 296, 6),
    (149, 296, 6),
    (150, 296, 6),
    (163, 296, 6),
    (165, 296, 6),
    (168, 296, 6),
    (16, 296, 6),
    (46, 296, 6),
    (54, 296, 6),
    (57, 296, 6),
    (43, 290, 6),
    (43, 304, 6),
    (43, 310, 6),
    (43, 325, 6),
    (43, 173, 6),
    (43, 196, 6),
    (43, 207, 6),
    (43, 234, 6),
    (43, 239, 6),
    (43, 246, 6),
    (43, 257, 6),
    (68, 293, 6),
    (118, 293, 6),
    (124, 293, 6),
    (125, 293, 6),
    (138, 293, 6),
    (142, 293, 6),
    (145, 293, 6),
    (148, 293, 6),
    (149, 293, 6),
    (153, 293, 6),
    (165, 293, 6),
    (168, 293, 6),
    (16, 293, 6),
    (55, 293, 6),
    (57, 293, 6),
    (44, 290, 6),
    (44, 320, 6),
    (7, 173, 6),
    (44, 174, 6),
    (44, 196, 6),
    (44, 207, 6),
    (7, 234, 6),
    (7, 239, 6),
    (44, 246, 6),
    (44, 257, 6),
    (118, 195, 6),
    (125, 195, 6),
    (138, 195, 6),
    (142, 195, 6),
    (145, 195, 6),
    (148, 195, 6),
    (153, 195, 6),
    (165, 195, 6),
    (168, 195, 6),
    (16, 195, 6),
    (55, 195, 6),
    (57, 195, 6),
    (82, 290, 6),
    (82, 310, 6),
    (82, 317, 6),
    (82, 325, 6),
    (82, 173, 6),
    (82, 174, 6),
    (82, 179, 6),
    (82, 188, 6),
    (82, 196, 6),
    (82, 207, 6),
    (82, 208, 6),
    (82, 212, 6),
    (82, 234, 6),
    (82, 239, 6),
    (82, 246, 6),
    (82, 256, 6),
    (82, 257, 6),
    (68, 327, 6),
    (118, 237, 6),
    (125, 237, 6),
    (138, 237, 6),
    (142, 237, 6),
    (145, 327, 6),
    (148, 237, 6),
    (149, 237, 6),
    (153, 237, 6),
    (165, 237, 6),
    (168, 237, 6),
    (16, 237, 6),
    (55, 237, 6),
    (57, 237, 6),
    (124, 310, 6),
    (124, 317, 6),
    (124, 332, 6),
    (124, 174, 6),
    (124, 175, 6),
    (124, 179, 6),
    (124, 188, 6),
    (124, 189, 6),
    (124, 208, 6),
    (124, 212, 6),
    (124, 227, 6),
    (124, 234, 6),
    (124, 239, 6),
    (124, 256, 6),
    (124, 257, 6),
    (96, 327, 6),
    (125, 327, 6),
    (129, 327, 6),
    (135, 327, 6),
    (138, 327, 6),
    (142, 327, 6),
    (165, 327, 6),
    (168, 327, 6),
    (16, 327, 6),
    (46, 327, 6),
    (57, 327, 6),
    (7, 174, 6),
    (7, 257, 6),
    (80, 328, 6),
    (145, 328, 6),
    (52, 174, 6),
    (52, 257, 6),
    (80, 292, 6),
    (145, 292, 6),
    (44, 291, 6),
    (44, 322, 6),
    (44, 173, 6),
    (44, 178, 6),
    (44, 198, 6),
    (44, 222, 6),
    (44, 223, 6),
    (44, 226, 6),
    (77, 292, 6),
    (108, 292, 6),
    (118, 292, 6),
    (134, 292, 6),
    (140, 292, 6),
    (148, 292, 6),
    (31, 292, 6),
    (43, 292, 6),
    (47, 292, 6),
    (55, 292, 6)
  ]

private def pathKeys : List PKey :=
  [
    (true, [11, 12, 14, 17, 52, 149, 258], [1, 2, 12, 13, 40, 43, 44, 59, 61, 64, 87, 91, 97, 104, 105, 106, 112, 116, 123, 127, 131, 137, 141, 144, 151, 203, 213, 224, 235, 243, 259, 261, 264, 266, 268, 271, 272, 274, 275, 281, 283, 284, 300, 313, 316, 329, 333, 335, 337, 339, 341], [(1, some 1091), (2, some 1092), (12, none), (13, some 1093), (40, some 1094), (43, some 1095), (44, some 1096), (59, some 1097), (61, some 1098), (64, some 1099), (87, some 1100), (91, some 1101), (97, some 1102), (104, some 1103), (105, some 1104), (106, some 1105), (112, some 1106), (116, some 1107), (123, some 1108), (127, some 1109), (131, some 1110), (137, some 1111), (141, some 1112), (144, some 1113), (151, some 1114), (203, some 1115), (213, some 1116), (224, some 1117), (235, some 1118), (243, some 1119), (259, some 1120), (261, some 1121), (264, some 1122), (266, some 1123), (268, some 1124), (271, some 1125), (272, some 1126), (274, some 1127), (275, some 1128), (281, some 1129), (283, some 1130), (284, some 1131), (300, some 1132), (313, some 1133), (316, some 1134), (329, some 1135), (333, some 1136), (335, some 1137), (337, some 1138), (339, some 1139), (341, some 1140)]),
    (true, [11, 14, 17, 52, 149, 194, 258, 297], [1, 3, 13, 14, 27, 43, 44, 59, 61, 87, 97, 106, 127, 131, 137, 141, 144, 149, 194, 224, 235, 243, 252, 259, 264, 266, 271, 272, 275, 277, 280, 283, 284, 285, 300, 313, 323, 337, 339], [(1, some 1141), (3, some 1142), (13, some 1143), (14, none), (27, some 1144), (43, some 1145), (44, some 1146), (59, some 1147), (61, some 1148), (87, some 1149), (97, some 1150), (106, some 1151), (127, some 1152), (131, some 1153), (137, some 1154), (141, some 1155), (144, some 1156), (149, none), (194, none), (224, some 1157), (235, some 1158), (243, some 1159), (252, some 1160), (259, some 1161), (264, some 1162), (266, some 1163), (271, some 1164), (272, some 1165), (275, some 1166), (277, some 1167), (280, some 1168), (283, some 1169), (284, some 1170), (285, some 1171), (300, some 1172), (313, some 1173), (323, some 1174), (337, some 1175), (339, some 1176)]),
    (true, [11, 14, 17, 52, 81, 149, 258, 297], [1, 2, 3, 13, 14, 35, 43, 44, 59, 61, 64, 87, 91, 97, 104, 105, 106, 112, 116, 127, 131, 137, 141, 144, 149, 151, 202, 224, 235, 243, 252, 259, 261, 264, 266, 271, 272, 274, 275, 277, 280, 283, 284, 285, 300, 313, 323, 337, 339], [(1, some 1177), (2, some 1178), (3, some 1179), (13, some 1180), (14, none), (35, some 1181), (43, some 1182), (44, some 1183), (59, some 1184), (61, some 1185), (64, some 1186), (87, some 1187), (91, some 1188), (97, some 1189), (104, some 1190), (105, some 1191), (106, some 1192), (112, some 1193), (116, some 1194), (127, some 1195), (131, some 1196), (137, some 1197), (141, some 1198), (144, some 1199), (149, none), (151, some 1200), (202, some 1201), (224, some 1157), (235, some 1158), (243, some 1159), (252, some 1160), (259, some 1202), (261, some 1203), (264, some 1162), (266, some 1163), (271, some 1164), (272, some 1165), (274, some 1204), (275, some 1166), (277, some 1167), (280, some 1168), (283, some 1169), (284, some 1170), (285, some 1171), (300, some 1172), (313, some 1173), (323, some 1174), (337, some 1175), (339, some 1176)]),
    (true, [11, 14, 17, 52, 258, 263], [1, 13, 14, 26, 27, 43, 44, 53, 59, 61, 66, 75, 87, 95, 97, 99, 106, 127, 131, 137, 141, 143, 144, 194, 224, 235, 243, 259, 263, 264, 266, 271, 272, 275, 277, 283, 284, 300, 313, 337, 339], [(1, some 1205), (13, some 1206), (14, none), (26, some 1207), (27, some 1208), (43, some 1209), (44, some 1210), (53, some 1211), (59, some 1212), (61, some 1213), (66, some 1214), (75, some 1215), (87, some 1216), (95, some 1217), (97, some 1218), (99, some 1219), (106, some 1220), (127, some 1221), (131, some 1222), (137, some 1223), (141, some 1224), (143, some 1225), (144, some 1226), (194, some 1227), (224, some 1228), (235, some 1229), (243, some 1230), (259, some 1231), (263, none), (264, some 1232), (266, some 1233), (271, some 1234), (272, some 1235), (275, some 1236), (277, some 1237), (283, some 1238), (284, some 1239), (300, some 1240), (313, some 1241), (337, some 1242), (339, some 1243)]),
    (true, [11, 17, 52, 185, 258, 299], [1, 11, 22, 26, 43, 44, 53, 59, 61, 62, 66, 75, 76, 87, 95, 97, 99, 106, 114, 131, 141, 143, 144, 185, 209, 224, 235, 248, 259, 263, 264, 272, 277, 284, 300, 330, 337], [(1, some 1244), (11, none), (22, some 1245), (26, some 1246), (43, some 1247), (44, some 1248), (53, some 1249), (59, some 1250), (61, some 1251), (62, some 1252), (66, some 1253), (75, some 1254), (76, some 1255), (87, some 1256), (95, some 1257), (97, some 1258), (99, some 1259), (106, some 1260), (114, some 1261), (131, some 1262), (141, some 1263), (143, some 1264), (144, some 1265), (185, none), (209, some 1266), (224, some 1267), (235, some 1268), (248, some 1269), (259, some 1270), (263, some 1271), (264, some 1272), (272, some 1273), (277, some 1274), (284, some 1275), (300, some 1276), (330, some 1277), (337, some 1278)]),
    (true, [11, 17, 52, 72, 258, 299], [1, 11, 13, 26, 27, 43, 44, 53, 59, 61, 62, 66, 75, 76, 87, 95, 97, 99, 106, 114, 127, 131, 137, 141, 143, 144, 194, 209, 224, 235, 243, 248, 259, 263, 264, 266, 271, 272, 275, 277, 283, 284, 300, 313, 330, 337, 339], [(1, some 1279), (11, none), (13, some 1280), (26, some 1281), (27, some 1282), (43, some 1283), (44, some 1284), (53, some 1285), (59, some 1286), (61, some 1287), (62, some 1288), (66, some 1289), (75, some 1290), (76, some 1291), (87, some 1292), (95, some 1293), (97, some 1294), (99, some 1295), (106, some 1296), (114, some 1297), (127, some 1298), (131, some 1299), (137, some 1300), (141, some 1301), (143, some 1302), (144, some 1303), (194, some 1304), (209, some 1305), (224, some 1306), (235, some 1307), (243, some 1308), (248, some 1309), (259, some 1310), (263, some 1311), (264, some 1312), (266, some 1313), (271, some 1314), (272, some 1315), (275, some 1316), (277, some 1317), (283, some 1318), (284, some 1319), (300, some 1320), (313, some 1321), (330, some 1322), (337, some 1323), (339, some 1324)]),
    (true, [7, 8, 17, 43, 52, 258, 296], [8, 21, 26, 43, 44, 48, 53, 59, 61, 62, 66, 75, 76, 87, 95, 97, 99, 114, 121, 126, 141, 143, 144, 183, 209, 235, 238, 242, 248, 251, 255, 259, 263, 264, 277, 279, 282, 301, 330, 337, 340], [(8, none), (21, some 1325), (26, some 1326), (43, none), (44, some 1327), (48, some 1328), (53, some 1329), (59, some 1330), (61, some 1331), (62, some 1332), (66, some 1333), (75, some 1334), (76, some 1335), (87, some 1336), (95, some 1337), (97, some 1338), (99, some 1339), (114, some 1340), (121, some 1341), (126, some 1342), (141, some 1343), (143, some 1344), (144, some 1345), (183, some 1346), (209, some 1347), (235, some 1348), (238, some 1349), (242, some 1350), (248, some 1351), (251, some 1352), (255, some 1353), (259, some 1354), (263, some 1355), (264, some 1356), (277, some 1357), (279, some 1358), (282, some 1359), (301, some 1360), (330, some 1361), (337, some 1362), (340, some 1363)]),
    (true, [7, 17, 43, 52, 258, 293, 296], [5, 7, 20, 26, 41, 43, 44, 60, 61, 66, 75, 83, 94, 95, 99, 121, 126, 133, 143, 144, 181, 231, 237, 238, 251, 255, 259, 262, 263, 267, 279, 282, 301, 338, 340], [(5, some 1364), (7, none), (20, some 1365), (26, some 1366), (41, some 1367), (43, none), (44, some 1327), (60, some 1368), (61, some 1331), (66, some 1333), (75, some 1334), (83, some 1369), (94, some 1370), (95, some 1337), (99, some 1339), (121, some 1371), (126, some 1372), (133, some 1373), (143, some 1344), (144, some 1374), (181, some 1375), (231, some 1376), (237, some 1377), (238, some 1378), (251, some 1379), (255, some 1380), (259, some 1381), (262, some 1382), (263, some 1383), (267, some 1384), (279, some 1385), (282, some 1386), (301, some 1387), (338, some 1388), (340, some 1389)]),
    (true, [7, 17, 44, 52, 195, 237, 258, 296, 327], [5, 7, 36, 44, 60, 61, 83, 94, 121, 126, 133, 144, 195, 231, 238, 251, 255, 259, 262, 267, 279, 282, 301, 327, 338, 340], [(5, some 1390), (7, none), (36, some 1391), (44, none), (60, some 1392), (61, some 1393), (83, some 1394), (94, some 1395), (121, some 1396), (126, some 1397), (133, some 1398), (144, some 1399), (195, none), (231, some 1400), (238, some 1401), (251, some 1402), (255, some 1403), (259, some 1404), (262, some 1405), (267, some 1406), (279, some 1407), (282, some 1408), (301, some 1409), (327, none), (338, some 1410), (340, some 1411)]),
    (true, [7, 17, 44, 52, 82, 237, 258, 296, 327], [5, 7, 26, 33, 41, 44, 60, 61, 66, 75, 83, 94, 95, 99, 121, 126, 133, 143, 144, 181, 231, 237, 238, 251, 255, 259, 262, 263, 267, 279, 282, 301, 327, 338, 340], [(5, some 1412), (7, none), (26, some 1413), (33, some 1414), (41, some 1415), (44, none), (60, some 1416), (61, some 1417), (66, some 1418), (75, some 1419), (83, some 1420), (94, some 1421), (95, some 1422), (99, some 1423), (121, some 1424), (126, some 1425), (133, some 1426), (143, some 1427), (144, some 1428), (181, some 1429), (231, some 1430), (237, none), (238, some 1431), (251, some 1432), (255, some 1433), (259, some 1434), (262, some 1435), (263, some 1436), (267, some 1437), (279, some 1438), (282, some 1439), (301, some 1440), (327, none), (338, some 1441), (340, some 1442)]),
    (true, [7, 17, 44, 52, 124, 258, 296, 327], [8, 26, 33, 44, 48, 61, 62, 66, 75, 76, 95, 99, 114, 121, 126, 143, 144, 181, 209, 238, 242, 248, 251, 255, 259, 263, 279, 282, 301, 327, 330, 340], [(8, some 1377), (26, some 1443), (33, some 1444), (44, none), (48, some 1445), (61, some 1446), (62, some 1447), (66, some 1448), (75, some 1449), (76, some 1450), (95, some 1451), (99, some 1452), (114, some 1453), (121, some 1454), (126, some 1455), (143, some 1456), (144, some 1457), (181, some 1429), (209, some 1458), (238, some 1459), (242, some 1460), (248, some 1461), (251, some 1462), (255, some 1463), (259, some 1434), (263, some 1145), (279, some 1464), (282, some 1465), (301, some 1466), (327, none), (330, some 1467), (340, some 1468)]),
    (true, [7, 17, 52, 258, 296, 327, 328], [61, 144, 193, 259, 327, 328], [(61, some 1469), (144, some 1470), (193, some 1471), (259, some 1472), (327, none), (328, none)]),
    (true, [17, 52, 258, 292, 296, 328], [61, 144, 193, 259, 327, 328], [(61, some 1473), (144, some 1474), (193, some 1475), (259, some 1476), (327, some 1327), (328, none)]),
    (true, [17, 44, 52, 258, 292, 296], [6, 38, 44, 60, 61, 65, 83, 85, 94, 109, 110, 113, 133, 144, 190, 221, 231, 247, 253, 259, 262, 315, 327, 331, 338], [(6, some 1477), (38, some 1478), (44, none), (60, some 1479), (61, some 1393), (65, some 1480), (83, some 1394), (85, some 1481), (94, some 1395), (109, some 1482), (110, some 1483), (113, some 1484), (133, some 1398), (144, some 1399), (190, some 1485), (221, some 1486), (231, some 1487), (247, some 1488), (253, some 1489), (259, some 1476), (262, some 1490), (315, some 1491), (327, some 1492), (331, some 1493), (338, some 1494)])
  ]

private def lookupWitness (wid : ℕ) : Option WKey :=
  if 1070 ≤ wid then witnessKeys[wid - 1070]? else none

private def lookupPath (pid : ℕ) : Option PKey :=
  if 50 ≤ pid then pathKeys[pid - 50]? else none

private def decodeWitness (w : WKey) : WitnessKey := ⟨w.1, w.2.1, w.2.2⟩

private def decodePath (p : PKey) : PathKey := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩

private def right3Metadata : IndexMetadata where
  boundCount := 341
  proofCount := 1494
  witnessCount := 1473
  pathCount := 63
  rectangleId := 6
  complement := lookupComplement
  pairNode := lookupPair
  witnessKey := fun wid => (lookupWitness wid).map decodeWitness
  pathKey := fun pid => (lookupPath pid).map decodePath

/- The complete source-faithfulness record will be assembled after the
   witness/path projection interfaces have been checked. -/


private def witnessKey (w : LateWitnessRow) : WKey := (w.lower, w.upper, w.rectangle)

private def pathKey (p : LatePath) : PKey :=
  (p.right3, p.incoming, p.required, p.implications)

private theorem array_project_suffix {α β : Type} (xs : Array α) (f : α → β)
    (fallback : α) (offset : ℕ) (keys : List β)
    (hkeys : (xs.toList.drop offset).map f = keys) (i : ℕ) :
    f (xs[offset + i]?.getD fallback) = keys[i]?.getD (f fallback) := by
  calc
    f (xs[offset + i]?.getD fallback) =
        (xs.toList.map f)[offset + i]?.getD (f fallback) := by
      rw [List.getElem?_map, Array.getElem?_toList]
      exact (Option.getD_map f fallback (xs[offset + i]?)).symm
    _ = ((xs.toList.map f).drop offset)[i]?.getD (f fallback) := by
      rw [List.getElem?_drop]
    _ = keys[i]?.getD (f fallback) := by
      rw [← List.map_drop, hkeys]

private theorem witness_row_projected (C : LateCatalog) (offset : ℕ) (keys : List WKey)
    (hkeys : (C.witnesses.toList.drop offset).map witnessKey = keys) (i : ℕ) :
    witnessKey (lateWitnessRow C (offset + i + 1)) = keys[i]?.getD (0, 0, 0) := by
  unfold lateWitnessRow
  rw [Nat.add_sub_cancel]
  exact array_project_suffix C.witnesses witnessKey ⟨0, 0, 0, fun _ _ => 0⟩ offset keys hkeys i

private theorem path_row_projected (C : LateCatalog) (offset : ℕ) (keys : List PKey)
    (hkeys : (C.paths.toList.drop offset).map pathKey = keys) (i : ℕ) :
    pathKey (latePath C (offset + i + 1)) = keys[i]?.getD (false, [], [], []) := by
  unfold latePath
  rw [Nat.add_sub_cancel]
  exact array_project_suffix C.paths pathKey ⟨false, [], [], [], [], [], []⟩ offset keys hkeys i

private theorem witnessKeys_eq :
    (lateCatalog.witnesses.toList.drop 1069).map witnessKey = witnessKeys := by
  change (((lateWitnessData1 ++ lateWitnessData2 ++ lateWitnessData3 ++
    lateWitnessData4 ++ lateWitnessData5 ++ lateWitnessData6 ++
    lateWitnessData7 ++ lateWitnessData8).toList.drop 1069).map witnessKey) = witnessKeys
  simp only [Array.toList_append, List.map_drop, List.map_append]
  rfl

private theorem pathKeys_eq :
    (lateCatalog.paths.toList.drop 49).map pathKey = pathKeys := by
  change (((latePathData1 ++ latePathData2 ++ latePathData3 ++
    latePathData4).toList.drop 49).map pathKey) = pathKeys
  simp only [Array.toList_append, List.map_drop, List.map_append]
  rfl

private theorem witness_projection (wid : ℕ) (hw : 1070 ≤ wid) :
    witnessKey (lateWitnessRow lateCatalog wid) = witnessKeys[wid - 1070]?.getD (0, 0, 0) := by
  have he : 1069 + (wid - 1070) + 1 = wid := by omega
  have h := witness_row_projected lateCatalog 1069 witnessKeys witnessKeys_eq (wid - 1070)
  exact Eq.mp (congrArg (fun n => witnessKey (lateWitnessRow lateCatalog n) =
    witnessKeys[wid - 1070]?.getD (0, 0, 0)) he) h

private theorem path_projection (pid : ℕ) (hp : 50 ≤ pid) :
    pathKey (latePath lateCatalog pid) = pathKeys[pid - 50]?.getD (false, [], [], []) := by
  have he : 49 + (pid - 50) + 1 = pid := by omega
  have h := path_row_projected lateCatalog 49 pathKeys pathKeys_eq (pid - 50)
  exact Eq.mp (congrArg (fun n => pathKey (latePath lateCatalog n) =
    pathKeys[pid - 50]?.getD (false, [], [], [])) he) h

private theorem witnessKey_fields (r : LateWitnessRow) (k : WKey)
    (h : witnessKey r = k) :
    r.lower = k.1 ∧ r.upper = k.2.1 ∧ r.rectangle = k.2.2 := by
  exact ⟨congrArg Prod.fst h, congrArg (fun x => x.2.1) h,
    congrArg (fun x => x.2.2) h⟩

private theorem lookupWitness_faithful (wid : ℕ) (w : WKey)
    (h : lookupWitness wid = some w) :
    (lateWitnessRow lateCatalog wid).lower = w.1 ∧
    (lateWitnessRow lateCatalog wid).upper = w.2.1 ∧
    (lateWitnessRow lateCatalog wid).rectangle = w.2.2 := by
  unfold lookupWitness at h
  split at h
  next hge =>
    have hs : witnessKeys[wid - 1070]?.getD (0, 0, 0) = w :=
      congrArg (fun o : Option WKey => o.getD (0, 0, 0)) h
    have he := (witness_projection wid hge).trans hs
    exact witnessKey_fields (lateWitnessRow lateCatalog wid) w he
  next => contradiction

private theorem pathKey_fields (r : LatePath) (k : PKey)
    (h : pathKey r = k) :
    r.right3 = k.1 ∧ r.incoming = k.2.1 ∧
    r.required = k.2.2.1 ∧ r.implications = k.2.2.2 := by
  exact ⟨congrArg Prod.fst h, congrArg (fun x => x.2.1) h,
    congrArg (fun x => x.2.2.1) h, congrArg (fun x => x.2.2.2) h⟩

private theorem lookupPath_faithful (pid : ℕ) (p : PKey)
    (h : lookupPath pid = some p) :
    (latePath lateCatalog pid).right3 = p.1 ∧
    (latePath lateCatalog pid).incoming = p.2.1 ∧
    (latePath lateCatalog pid).required = p.2.2.1 ∧
    (latePath lateCatalog pid).implications = p.2.2.2 := by
  unfold lookupPath at h
  split at h
  next hge =>
    have hs : pathKeys[pid - 50]?.getD (false, [], [], []) = p :=
      congrArg (fun o : Option PKey => o.getD (false, [], [], [])) h
    have he := (path_projection pid hge).trans hs
    exact pathKey_fields (latePath lateCatalog pid) p he
  next => contradiction

private theorem right3_faithful :
    MetadataFaithful lateCatalog right3Metadata (lateRootRectangle true) := by
  refine {
    bound_count := ?_
    proof_count := ?_
    witness_count := ?_
    path_count := ?_
    complement := ?_
    pair_node := ?_
    witness_key := ?_
    path_key := ?_
    rectangle := ?_
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
  · intro pid wid h
    exact lookupPair_faithful pid wid h
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
  · rfl

private theorem right3_check :
    checkDecision right3Metadata true [17, 52, 258] (lateTree true) = true := by
  decide

end DiscoveryFreimanReflectedMetadata

open DiscoveryFreimanReflectedMetadata in
theorem solution :
    Freiman.lateDecisionValid Freiman.lateCatalog true Freiman.lateRootBounds
      (Freiman.lateRootRectangle true) (Freiman.lateTree true) := by
  exact checkDecision_sound lateCatalog right3Metadata (lateRootRectangle true)
    right3_faithful true [17, 52, 258] (lateTree true) right3_check

#print axioms solution
