-- Prove2me | solution 1 for Freiman.trunk_bindings_15_000_100
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:38:33.623235+00:00
-- url     : https://prove2.me/submissions/e4e0e8e1-39fb-449b-bfe6-965b135895a6

import Definitions.Def_Freiman_trunkFast
import Theorems.Thm_Freiman_trunkFast_correctness
set_option Elab.async false
open Freiman Freiman.TrunkFast
private def intCode (z : ℤ) : ℕ := if z < 0 then 2*z.natAbs+1 else 2*z.natAbs
private def proj (b : CertBound) : ℕ :=
  [b.lower.toNat,b.strict.toNat,intCode b.threshold.c.a.num,b.threshold.c.a.den,
   intCode b.threshold.x0.a.num,b.threshold.x0.a.den,intCode b.threshold.c.b.num,
   b.threshold.c.b.den,intCode b.threshold.x0.b.num,b.threshold.x0.b.den].foldl
    (fun acc n => ((acc+n+17)*(acc+n+17)+3*acc) % 1000000007) 7
private def fingerprint (bs : List CertBound) : ℕ := ((bs.map proj).toFinset.sum id)

private theorem fingerprint_congr {cs bs : List CertBound} (heq : cs.toFinset = bs.toFinset) :
    fingerprint cs = fingerprint bs := by
  have hm : ∀ b, b ∈ cs ↔ b ∈ bs := by
    intro b
    have h := congrArg (fun s : Finset CertBound => b ∈ s) heq
    simpa using Iff.of_eq h
  have hi : (cs.map proj).toFinset = (bs.map proj).toFinset := by
    ext z
    simp only [List.mem_toFinset,List.mem_map,hm]
  exact congrArg (fun s : Finset ℕ => s.sum id) hi
private theorem parents_of_fingerprints (raw : List (List CertBound))
    (h : (raw.map fingerprint).Nodup) : raw.Pairwise (fun cs bs => cs.toFinset ≠ bs.toFinset) := by
  have h' : raw.Pairwise (fun cs bs => fingerprint cs ≠ fingerprint bs) := List.pairwise_map.mp h
  exact h'.imp fun hne heq => hne (fingerprint_congr heq)
private def rawParent (a b : List CertBound × LowerHistoryComparison) : Option (List CertBound) :=
  let base := a.1 ++ b.1 ++ [lowerHistoryHN,lowerHistoryZero]
  match a.2,b.2 with
  | .impossible,_ | _,.impossible => none
  | .automatic,.automatic => some base
  | .bound g,.automatic | .automatic,.bound g => some (g::base)
  | .bound g,.bound h => some (g::h::base)
private def branchCode (a : List CertBound × LowerHistoryComparison) : List ℕ × Option (Option ℕ) :=
  (a.1.map proj, match a.2 with
    | .impossible => none
    | .automatic => some none
    | .bound b => some (some (proj b)))
private def parentCode (hn zero : ℕ) (a b : List ℕ × Option (Option ℕ)) : Option (List ℕ) :=
  match a.2,b.2 with
  | none,_ | _,none => none
  | some ga,some gb => some (ga.toList ++ gb.toList ++ a.1 ++ b.1 ++ [hn,zero])
private theorem parentCode_map (a b : List CertBound × LowerHistoryComparison) :
    (rawParent a b).map (List.map proj) = parentCode (proj lowerHistoryHN) (proj lowerHistoryZero) (branchCode a) (branchCode b) := by
  rcases a with ⟨ca,ga⟩
  rcases b with ⟨cb,gb⟩
  cases ga <;> cases gb <;> simp [rawParent,parentCode,branchCode,List.map_append,List.append_assoc]
private theorem rawCodes_map (A B : List (List CertBound × LowerHistoryComparison)) :
    (A.flatMap (fun a => B.filterMap (rawParent a))).map (List.map proj) =
    (A.map branchCode).flatMap (fun a => (B.map branchCode).filterMap (parentCode (proj lowerHistoryHN) (proj lowerHistoryZero) a)) := by
  simp only [List.map_flatMap,List.map_filterMap,List.flatMap_map,List.filterMap_map,Function.comp_apply]
  apply congrArg (fun f => A.flatMap f)
  funext a
  apply congrArg (fun f => B.filterMap f)
  funext b
  exact parentCode_map a b
private theorem trunkCodes_map (C : LowerHistoryContext) :
    (trunkRawParents C).map (List.map proj) =
    ((trunkBranches C ⟨([2],[]),true,([1],[]),false,false,[]⟩).map branchCode).flatMap (fun a =>
    ((trunkBranches C ⟨([1],[]),true,([2],[]),false,false,[]⟩).map branchCode).filterMap (parentCode (proj lowerHistoryHN) (proj lowerHistoryZero) a)) := by
  exact rawCodes_map _ _

private def codesA15 : List (List ℕ × Option (Option ℕ)) := [([112911326, 882722351], some (some 626279719)),
 ([112911326, 991976176], some (some 626279719)),
 ([728891584, 60072750, 649066977, 882722351], some (some 626279719)),
 ([728891584, 60072750, 649066977, 991976176], some (some 626279719)),
 ([728891584, 60072750, 595767334, 882722351], some (some 416338889)),
 ([728891584, 60072750, 595767334, 991976176], some (some 416338889)),
 ([728891584, 476573349, 881768834, 882722351], some (some 626279719)),
 ([728891584, 476573349, 881768834, 991976176], some (some 626279719)),
 ([728891584, 476573349, 159503643, 882722351], some (some 753260783)),
 ([728891584, 476573349, 159503643, 991976176], some (some 753260783))]
private def codesB15 : List (List ℕ × Option (Option ℕ)) := [([882722351, 112911326], some none),
 ([882722351, 728891584], some none),
 ([991976176, 466397207, 55717250, 112911326], some none),
 ([991976176, 466397207, 55717250, 728891584], some none),
 ([991976176, 466397207, 649614909, 112911326], some none),
 ([991976176, 466397207, 649614909, 728891584], some none),
 ([991976176, 827878947, 143171926, 112911326], some none),
 ([991976176, 827878947, 143171926, 728891584], some none),
 ([991976176, 827878947, 222803470, 112911326], some none),
 ([991976176, 827878947, 222803470, 728891584], some none)]

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
private def decodeThresholdBound (b : ℕ × Bool × Bool) : CertBound :=
  ⟨b.2.1,b.2.2,(fastBound b.1).threshold⟩
private def decodeGoalBranch (a : List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) : List CertBound × LowerHistoryComparison :=
  (a.1.map decodeThresholdBound, match a.2 with
    | none => .impossible
    | some none => .automatic
    | some (some b) => .bound (decodeThresholdBound b))
private def thresholdClasses : Array ℕ := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 2, 6, 13, 13, 3, 10, 17, 18, 17, 20, 18, 20, 23, 9, 4, 26, 27, 26, 29, 30, 31, 32, 33,
 34, 31, 36, 37, 32, 39, 37, 41, 33, 43, 44, 45, 46, 45, 48, 49, 50, 51, 52, 53, 52, 55, 56, 57, 56, 59, 51, 61, 62, 50,
 64, 65, 64, 67, 68, 69, 70, 71, 72, 73, 70, 75, 72, 77, 75, 69, 80, 81, 82, 83, 83, 85, 86, 87, 88, 89, 90, 91, 92, 90,
 30, 95, 95, 97, 91, 99, 100, 101, 102, 89, 104, 102, 106, 107, 108, 109, 110, 111, 112, 113, 114, 108, 112, 117, 117,
 119, 113, 121, 122, 123, 109, 125, 126, 125, 128, 129, 130, 110, 132, 133, 133, 135, 136, 132, 136, 139, 1, 23, 27,
 143, 29, 145, 146, 147, 148, 147, 150, 151, 152, 153, 154, 155, 156, 157, 155, 159, 160, 156, 162, 162, 164, 165, 166,
 8, 168, 168, 143, 145, 146, 148, 150, 151, 176, 177, 7, 179, 180, 181, 182, 183, 184, 181, 186, 187, 186, 189, 184,
 191, 189, 179, 194, 195, 196, 197, 182, 199, 197, 201, 202, 183, 204, 205, 206, 205, 208, 206, 210, 208, 212, 213, 210,
 215, 213, 217, 218, 219, 220, 221, 222, 223, 224, 225, 176, 227, 228, 228, 230, 231, 232, 233, 234, 235, 236, 231, 238,
 239, 236, 239, 242, 234, 233, 245, 246, 235, 248, 249, 248, 251, 249, 253, 254, 251, 254, 257, 246, 259, 260, 261, 262,
 263, 264, 263, 266, 259, 261, 269, 269, 271, 260, 273, 274, 275, 262, 274, 275, 279, 280, 280, 282, 283, 279, 285, 283,
 287, 288, 288, 290, 291, 292, 291, 294, 177, 296, 297, 298, 299, 300, 301, 299, 303, 304, 303, 301, 307, 307, 309, 310,
 311, 312, 298, 314, 315, 316, 297, 318, 319, 320, 321, 322, 323, 321, 325, 322, 327, 325, 320, 319, 331, 332, 332, 334,
 335, 336, 337, 331, 337, 340, 341, 342, 343, 344, 345, 346, 347, 346, 349, 350, 349, 352, 347, 354, 352, 356, 357, 358,
 343, 360, 361, 362, 344, 364, 365, 366, 366, 365, 369, 370, 370, 372, 373, 369, 375, 373, 377, 378, 379, 380, 381, 381,
 383, 384, 385, 383, 384, 388, 388, 390, 391, 377, 393, 394, 395, 379, 395, 398, 399, 400, 380, 402, 403, 404, 405, 406,
 407, 403, 409, 406, 411, 409, 404, 414, 415, 405, 414, 418, 419, 420, 421, 415, 421, 424, 425, 426, 427, 428, 429, 430,
 431, 432, 428, 434, 427, 436, 430, 436, 439, 432, 441, 431, 443, 444, 445, 446, 447, 444, 449, 445, 451, 449, 446, 443,
 455, 456, 456, 458, 459, 460, 461, 455, 461, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 476,
 479, 479, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 490, 494, 495, 496, 497, 497, 499, 500, 501, 502,
 503, 504, 505, 506, 507, 296, 509, 510, 511, 512, 513, 510, 515, 516, 517, 511, 519, 520, 519, 522, 523, 524, 525, 526,
 526, 528, 529, 525, 531, 529, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550,
 551, 551]
private def thresholdClass (id : ℕ) : ℕ := thresholdClasses[id-1]?.getD 0

private def classValidIds : List ℕ := [23, 3, 15, 16, 10, 19, 20, 21, 33, 43, 36, 48, 88, 29, 92, 94, 98, 102, 103, 141, 144, 30, 167, 8, 171, 90, 145, 53, 7, 55, 60, 64, 63, 17, 18, 147, 178, 177, 97, 95, 149, 174, 150, 295, 318, 323, 327, 329, 333, 337, 338, 377, 379, 381, 378, 385, 390, 397, 402, 407, 411, 413, 417, 421, 422, 427, 430, 428, 429, 438, 441, 447, 451, 453, 457, 461, 462, 489, 491, 492, 493, 479, 497, 442, 52, 57, 321, 476]
private theorem thresholdClass_key : ∀ i ∈ classValidIds,
    i = thresholdClass i ∨ (fastBound i).threshold = (fastBound (thresholdClass i)).threshold := by decide +kernel
private theorem threshold_class_of_range (i : ℕ) (hi : i ∈ classValidIds) :
    (fastBound i).threshold = (fastBound (thresholdClass i)).threshold := by
  rcases thresholdClass_key i hi with he | he
  · rw [← he]
  · exact he
private def codeUseBounds (w : TrunkWitness) (l u : ℕ × Bool × Bool) : Prop :=
  l.2.1 = true ∧ u.2.1 = false ∧
  w.lowerId ∈ classValidIds ∧ w.upperId ∈ classValidIds ∧
  l.1 = thresholdClass w.lowerId ∧ u.1 = thresholdClass w.upperId ∧
  ((w.diagonal = 0 ∧ 0 < w.margin) ∨ l.2.2 = true ∨ u.2.2 = true)
private theorem codeUseBounds_sound (w : TrunkWitness) (l u : ℕ × Bool × Bool)
    (h : codeUseBounds w l u) : trunkUseBoundsFast w (decodeThresholdBound l) (decodeThresholdBound u) := by
  rcases h with ⟨hl,hu,hll,hul,hle,hue,hs⟩
  refine ⟨hl,hu,?_,?_,hs⟩
  · change (fastBound l.1).threshold = (fastBound w.lowerId).threshold
    rw [hle,← threshold_class_of_range w.lowerId hll]
  · change (fastBound u.1).threshold = (fastBound w.upperId).threshold
    rw [hue,← threshold_class_of_range w.upperId hul]
private def codeLeafBound (R : CertRectangle) (bs : List (ℕ × Bool × Bool)) (id : ℕ) (sign : ℤ) : Prop :=
  0 < id ∧ id ≤ 8656 ∧
  (fastWitness id).diagonal = sign ∧
  section14RectangleContains (fastWitness id).rectangle R ∧
  (fastWitness id).lowerId ∈ classValidIds ∧ (fastWitness id).upperId ∈ classValidIds ∧
  ∃ l ∈ bs, l.2.1 = true ∧ l.1 = thresholdClass (fastWitness id).lowerId ∧
    ∃ u ∈ bs, u.2.1 = false ∧ u.1 = thresholdClass (fastWitness id).upperId ∧
      (((fastWitness id).diagonal = 0 ∧ 0 < (fastWitness id).margin) ∨ l.2.2 = true ∨ u.2.2 = true)
private theorem codeLeafBound_sound (R : CertRectangle) (bs : List (ℕ × Bool × Bool)) (id : ℕ) (sign : ℤ)
    (h : codeLeafBound R bs id sign) : trunkLeafBoundFast R (bs.map decodeThresholdBound) id sign := by
  rcases h with ⟨hlo,hhi,hdiag,hrect,hll,hul,l,hl,hloflag,hloid,u,hu,hupflag,hupid,hstrict⟩
  refine ⟨hlo,hhi,hdiag,hrect,decodeThresholdBound l,List.mem_map.mpr ⟨l,hl,rfl⟩,
    decodeThresholdBound u,List.mem_map.mpr ⟨u,hu,rfl⟩,?_⟩
  exact codeUseBounds_sound _ _ _ ⟨hloflag,hupflag,hll,hul,hloid,hupid,hstrict⟩
private def codeTreeBound (R : CertRectangle) (bs : List (ℕ × Bool × Bool)) : TrunkTree → Prop
  | .pair id => codeLeafBound R bs id 0
  | .split axis left right =>
    codeTreeBound (trunkRectangleHalf R axis false) bs left ∧
    codeTreeBound (trunkRectangleHalf R axis true) bs right
  | .diagonal negative positive => codeLeafBound R bs negative (-1) ∧ codeLeafBound R bs positive 1
  | .boundary => trunkBoundaryBound R (bs.map decodeThresholdBound)
private instance decCodeTreeBound (R : CertRectangle) (bs : List (ℕ × Bool × Bool)) :
    ∀ t : TrunkTree, Decidable (codeTreeBound R bs t)
  | .pair id => by unfold codeTreeBound codeLeafBound section14RectangleContains; infer_instance
  | .split axis left right => by
      unfold codeTreeBound
      have := decCodeTreeBound (trunkRectangleHalf R axis false) bs left
      have := decCodeTreeBound (trunkRectangleHalf R axis true) bs right
      infer_instance
  | .diagonal negative positive => by
      unfold codeTreeBound codeLeafBound section14RectangleContains
      infer_instance
  | .boundary => by unfold codeTreeBound trunkBoundaryBound certThresholdDataValid; infer_instance
private theorem codeTreeBound_sound (t : TrunkTree) (R : CertRectangle) (bs : List (ℕ × Bool × Bool))
    (h : codeTreeBound R bs t) : trunkTreeBoundFast R (bs.map decodeThresholdBound) t := by
  induction t generalizing R with
  | pair id => exact codeLeafBound_sound _ _ _ _ h
  | split axis left right ihl ihr => exact ⟨ihl _ h.1,ihr _ h.2⟩
  | diagonal negative positive => exact ⟨codeLeafBound_sound _ _ _ _ h.1,codeLeafBound_sound _ _ _ _ h.2⟩
  | boundary => exact h
private def codeComplement (b : ℕ × Bool × Bool) : ℕ × Bool × Bool := (b.1,!b.2.1,!b.2.2)
private theorem decodeComplement (b : ℕ × Bool × Bool) :
    decodeThresholdBound (codeComplement b) = lowerHistoryComplement (decodeThresholdBound b) := rfl
private def codeResidual (parents : List (List (ℕ × Bool × Bool))) (cuts : List (ℕ × Bool × Bool))
    (goals : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))))
    (parent : ℕ) (branch : ℤ) : List (ℕ × Bool × Bool) :=
  let b := goals[branch.toNat]?.getD ([],none)
  cuts ++ parents[parent]?.getD [] ++ b.1 ++
    match b.2 with | some (some a) => [codeComplement a] | _ => []
private theorem codedBranch_eq (S : TrunkState) (pi goal : ℕ) (branch : ℤ)
    (codes : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))))
    (he : trunkGoalBranches S pi goal = codes.map decodeGoalBranch) :
    trunkBranch S pi goal branch = decodeGoalBranch (codes[branch.toNat]?.getD ([],none)) := by
  unfold trunkBranch
  rw [he,List.getElem?_map]
  exact Option.getD_map decodeGoalBranch ([],none) codes[branch.toNat]?
private theorem codedParent_eq (codes : List (List (ℕ × Bool × Bool))) (i : ℕ) :
    (codes.map (List.map decodeThresholdBound))[i]?.getD [] =
      (codes[i]?.getD []).map decodeThresholdBound := by
  rw [List.getElem?_map]
  exact Option.getD_map (List.map decodeThresholdBound) [] codes[i]?
private theorem codeResidual_eq (S : TrunkState) (pi parent goal : ℕ) (branch : ℤ)
    (parents : List (List (ℕ × Bool × Bool))) (cuts : List (ℕ × Bool × Bool))
    (goals : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))))
    (hpar : trunkRawParents S.context = parents.map (List.map decodeThresholdBound))
    (hcut : (trunkPlanAt S pi).cuts = cuts.map decodeThresholdBound)
    (hgoal : trunkGoalBranches S pi goal = goals.map decodeGoalBranch) :
    trunkResidualFast S pi parent goal branch = (codeResidual parents cuts goals parent branch).map decodeThresholdBound := by
  unfold trunkResidualFast codeResidual
  rw [hcut,hpar,codedParent_eq,codedBranch_eq S pi goal branch goals hgoal]
  generalize goals[branch.toNat]?.getD ([],none) = b
  rcases b with ⟨bs,cmp⟩
  cases cmp with
  | none => simp [decodeGoalBranch,List.map_append]
  | some cmp =>
    cases cmp <;> simp [decodeGoalBranch,List.map_append,decodeComplement]
private def codeGroupValid (S : TrunkState) (parents : List (List (ℕ × Bool × Bool)))
    (cuts : ℕ → List (ℕ × Bool × Bool))
    (goals : ℕ → ℕ → List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))))
    (g : TrunkGroup) : Prop :=
  g.plan < (trunkSourcePlans S.context).length ∧ g.goal ≤ (trunkSpecs (trunkPlanAt S g.plan)).length ∧
  (∀ p ∈ g.parents, p < parents.length) ∧
  ∀ bt ∈ g.branches,
    ((g.goal = 0 ∧ bt.1 = -1) ∨ (0 < g.goal ∧ 0 ≤ bt.1 ∧ bt.1.toNat < (goals g.plan g.goal).length)) ∧
    ((goals g.plan g.goal)[bt.1.toNat]?.getD ([],none)).2 ≠ some none ∧
    ∀ p ∈ g.parents, codeTreeBound S.rectangle (codeResidual parents (cuts g.plan) (goals g.plan g.goal) p bt.1) bt.2
private theorem codeGroupValid_sound (k : Fin 16) (parents : List (List (ℕ × Bool × Bool)))
    (cuts : ℕ → List (ℕ × Bool × Bool))
    (goals : ℕ → ℕ → List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))))
    (g : TrunkGroup)
    (hpar : trunkRawParents (trunkCatalog.states k).context = parents.map (List.map decodeThresholdBound))
    (hcut : (trunkPlanAt (trunkCatalog.states k) g.plan).cuts = (cuts g.plan).map decodeThresholdBound)
    (hgoal : trunkGoalBranches (trunkCatalog.states k) g.plan g.goal = (goals g.plan g.goal).map decodeGoalBranch)
    (h : codeGroupValid (trunkCatalog.states k) parents cuts goals g) : trunkGroupValidFast k g := by
  rcases h with ⟨hp,hg,hparents,hb⟩
  refine ⟨hp,hg,?_,?_⟩
  · simpa only [hpar,List.length_map] using hparents
  · intro bt hbt
    obtain ⟨hr,ha,ht⟩ := hb bt hbt
    refine ⟨?_,?_,?_⟩
    · simpa only [hgoal,List.length_map] using hr
    · rw [codedBranch_eq _ _ _ _ _ hgoal]
      generalize he : (goals g.plan g.goal)[bt.1.toNat]?.getD ([],none) = b at *
      rcases b with ⟨bs,cmp⟩
      cases cmp with
      | none => simp [decodeGoalBranch]
      | some cmp =>
        cases cmp <;> simp_all [decodeGoalBranch]
    · intro p hpg
      rw [codeResidual_eq _ _ _ _ _ parents (cuts g.plan) (goals g.plan g.goal) hpar hcut hgoal]
      exact codeTreeBound_sound _ _ _ (ht p hpg)
private def codeHN : ℕ × Bool × Bool := (8, false, false)
private def codeZero : ℕ × Bool × Bool := (5, true, true)

private theorem hDecodeHN : decodeThresholdBound codeHN = lowerHistoryHN := by decide +kernel
private theorem hDecodeZero : decodeThresholdBound codeZero = lowerHistoryZero := by decide +kernel
private def codeRawParent (a b : List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) : Option (List (ℕ × Bool × Bool)) :=
  match a.2,b.2 with
  | none,_ | _,none => none
  | some ga,some gb => some (ga.toList ++ gb.toList ++ a.1 ++ b.1 ++ [codeHN,codeZero])
private theorem codeRawParent_map (a b : List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) :
    (codeRawParent a b).map (List.map decodeThresholdBound) = rawParent (decodeGoalBranch a) (decodeGoalBranch b) := by
  rcases a with ⟨ca,ga⟩
  rcases b with ⟨cb,gb⟩
  cases ga with
  | none => simp [codeRawParent,decodeGoalBranch,rawParent]
  | some ga =>
    cases gb with
    | none => cases ga <;> simp [codeRawParent,decodeGoalBranch,rawParent]
    | some gb =>
      cases ga <;> cases gb <;>
        simp [codeRawParent,decodeGoalBranch,rawParent,List.map_append,List.append_assoc,hDecodeHN,hDecodeZero]
private theorem codeParents_map (A B : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool)))) :
    (A.flatMap (fun a => B.filterMap (codeRawParent a))).map (List.map decodeThresholdBound) =
    (A.map decodeGoalBranch).flatMap (fun a => (B.map decodeGoalBranch).filterMap (rawParent a)) := by
  simp only [List.map_flatMap,List.map_filterMap,List.flatMap_map,List.filterMap_map,Function.comp_apply]
  apply congrArg (fun f => A.flatMap f)
  funext a
  apply congrArg (fun f => B.filterMap f)
  funext b
  exact codeRawParent_map a b
private def thresholdParentA15 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(3, false, false), (10, false, false)], some (some (23, true, false))),
 ([(3, false, false), (10, true, true)], some (some (23, true, false))),
 ([(3, true, true), (30, false, false), (29, false, true), (10, false, false)], some (some (23, true, false))),
 ([(3, true, true), (30, false, false), (29, false, true), (10, true, true)], some (some (23, true, false))),
 ([(3, true, true), (30, false, false), (29, true, false), (10, false, false)], some (some (145, true, false))),
 ([(3, true, true), (30, false, false), (29, true, false), (10, true, true)], some (some (145, true, false))),
 ([(3, true, true), (30, true, true), (147, true, true), (10, false, false)], some (some (23, true, false))),
 ([(3, true, true), (30, true, true), (147, true, true), (10, true, true)], some (some (23, true, false))),
 ([(3, true, true), (30, true, true), (147, false, false), (10, false, false)], some (some (150, true, false))),
 ([(3, true, true), (30, true, true), (147, false, false), (10, true, true)], some (some (150, true, false)))]
private def thresholdParentB15 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(10, false, false), (3, false, false)], some none),
 ([(10, false, false), (3, true, true)], some none),
 ([(10, true, true), (18, false, false), (17, false, true), (3, false, false)], some none),
 ([(10, true, true), (18, false, false), (17, false, true), (3, true, true)], some none),
 ([(10, true, true), (18, false, false), (17, true, false), (3, false, false)], some none),
 ([(10, true, true), (18, false, false), (17, true, false), (3, true, true)], some none),
 ([(10, true, true), (18, true, true), (20, true, true), (3, false, false)], some none),
 ([(10, true, true), (18, true, true), (20, true, true), (3, true, true)], some none),
 ([(10, true, true), (18, true, true), (20, false, false), (3, false, false)], some none),
 ([(10, true, true), (18, true, true), (20, false, false), (3, true, true)], some none)]

private def codedParents15 : List (List (ℕ × Bool × Bool)) :=
  thresholdParentA15.flatMap (fun a => thresholdParentB15.filterMap (codeRawParent a))
private theorem hThresholdParentA15 : trunkBranches (trunkCatalog.states 15).context ⟨([2],[]),true,([1],[]),false,false,[]⟩ = thresholdParentA15.map decodeGoalBranch := by decide +kernel
private theorem hThresholdParentB15 : trunkBranches (trunkCatalog.states 15).context ⟨([1],[]),true,([2],[]),false,false,[]⟩ = thresholdParentB15.map decodeGoalBranch := by decide +kernel
private theorem hCodedParents15 : trunkRawParents (trunkCatalog.states 15).context = codedParents15.map (List.map decodeThresholdBound) := by
  unfold trunkRawParents codedParents15
  rw [hThresholdParentA15,hThresholdParentB15,codeParents_map]
  rfl

private theorem hHN : proj lowerHistoryHN = 466397207 := by decide +kernel
private theorem hZero : proj lowerHistoryZero = 559802771 := by decide +kernel

private theorem hA15 : (trunkBranches (trunkCatalog.states 15).context ⟨([2],[]),true,([1],[]),false,false,[]⟩).map branchCode = codesA15 := by
  rw [hThresholdParentA15]
  decide +kernel
private theorem hB15 : (trunkBranches (trunkCatalog.states 15).context ⟨([1],[]),true,([2],[]),false,false,[]⟩).map branchCode = codesB15 := by
  rw [hThresholdParentB15]
  decide +kernel
private def fprints15 : List ℕ := [2648113374, 3377004958, 3695806800, 4424698384, 4289704459, 5018596043, 4611140423, 5340032007, 4690771967, 5419663551, 3640089550, 4368981134, 2813084449, 3541976033, 3406982108, 4135873692, 3728418072, 4457309656, 3808049616, 4536941200, 4086144685, 3973233359, 5133838111, 5020926785, 5727735770, 5614824444, 6049171734, 5936260408, 6128803278, 6015891952, 5078120861, 4965209535, 4251115760, 4138204434, 4845013419, 4732102093, 5166449383, 5053538057, 5246080927, 5133169601, 3822904212, 3709992886, 4870597638, 4757686312, 5464495297, 5351583971, 5785931261, 5673019935, 5865562805, 5752651479, 4814880388, 4701969062, 3987875287, 3874963961, 4581772946, 4468861620, 4903208910, 4790297584, 4982840454, 4869929128, 4735347141, 4622435815, 5783040567, 5670129241, 6376938226, 6264026900, 6698374190, 6585462864, 6778005734, 6665094408, 5727323317, 5614411991, 4900318216, 4787406890, 5494215875, 5381304549, 5815651839, 5702740513, 5895283383, 5782372057, 4140063014, 4027151688, 5187756440, 5074845114, 5781654099, 5668742773, 6103090063, 5990178737, 6182721607, 6069810281, 5132039190, 5019127864, 4305034089, 4192122763, 4898931748, 4786020422, 5220367712, 5107456386, 5299999256, 5187087930]
private theorem hprints15 : (trunkRawParents (trunkCatalog.states 15).context).map fingerprint = fprints15 := by
  have hm (L : List (List CertBound)) :
      L.map fingerprint = (L.map (List.map proj)).map (fun cs => cs.toFinset.sum id) := by
    rw [List.map_map]; rfl
  rw [hm,trunkCodes_map,hA15,hB15,hHN,hZero]
  decide +kernel
private theorem hPar15 : trunkParents (trunkCatalog.states 15).context = trunkRawParents (trunkCatalog.states 15).context := by
  apply Freiman.trunkFast_correctness.1
  apply parents_of_fingerprints
  rw [hprints15]
  apply (List.perm_insertionSort (fun a b : ℕ => a ≤ b) fprints15).nodup_iff.mp
  have hs : (List.insertionSort (fun a b : ℕ => a ≤ b) fprints15).IsChain (fun a b => a < b) := by
    decide +kernel
  exact (List.isChain_iff_pairwise.mp hs).imp (fun h => Nat.ne_of_lt h)


private def goalCodes15_0_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([], none)]
private def goalCodes15_0_2 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(10, false, false), (4, false, false), (33, false, true)], some (some (36, true, true))),
 ([(10, false, false), (4, false, false), (33, true, false)], some (some (43, true, true))),
 ([(10, false, false), (4, true, true), (45, true, true)], some (some (36, true, true))),
 ([(10, false, false), (4, true, true), (45, false, false)], some (some (48, true, true)))]
private def goalCodes15_0_5 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(10, true, true), (50, false, true), (51, false, true), (18, false, true), (52, false, true)],
  some (some (53, false, true))),
 ([(10, true, true), (50, false, true), (51, false, true), (18, false, true), (52, true, false)],
  some (some (55, false, true))),
 ([(10, true, true), (50, false, true), (51, false, true), (18, true, false), (56, true, true)],
  some (some (53, false, true))),
 ([(10, true, true), (50, false, true), (51, false, true), (18, true, false), (56, false, false)],
  some (some (57, false, true))),
 ([(10, true, true), (50, false, true), (51, true, false), (18, false, true), (52, false, true)],
  some (some (59, false, true))),
 ([(10, true, true), (50, false, true), (51, true, false), (18, false, true), (52, true, false)],
  some (some (61, false, true))),
 ([(10, true, true), (50, false, true), (51, true, false), (18, true, false), (56, true, true)],
  some (some (59, false, true))),
 ([(10, true, true), (50, false, true), (51, true, false), (18, true, false), (56, false, false)],
  some (some (62, false, true))),
 ([(10, true, true), (50, true, false), (64, true, true), (18, false, true), (52, false, true)],
  some (some (53, false, true))),
 ([(10, true, true), (50, true, false), (64, true, true), (18, false, true), (52, true, false)],
  some (some (55, false, true))),
 ([(10, true, true), (50, true, false), (64, true, true), (18, true, false), (56, true, true)],
  some (some (53, false, true))),
 ([(10, true, true), (50, true, false), (64, true, true), (18, true, false), (56, false, false)],
  some (some (57, false, true))),
 ([(10, true, true), (50, true, false), (64, false, false), (18, false, true), (52, false, true)],
  some (some (65, false, true))),
 ([(10, true, true), (50, true, false), (64, false, false), (18, false, true), (52, true, false)],
  some (some (67, false, true))),
 ([(10, true, true), (50, true, false), (64, false, false), (18, true, false), (56, true, true)],
  some (some (65, false, true))),
 ([(10, true, true), (50, true, false), (64, false, false), (18, true, false), (56, false, false)],
  some (some (68, false, true)))]
private def goalCodes15_0_7 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(3, false, false), (6, false, false), (69, false, true)], some (some (73, true, true))),
 ([(3, false, false), (6, false, false), (69, true, false)], some (some (81, true, true))),
 ([(3, false, false), (6, true, true), (83, true, true)], some (some (73, true, true))),
 ([(3, false, false), (6, true, true), (83, false, false)], some (some (86, true, true)))]
private def goalCodes15_0_10 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(3, true, true), (89, false, true), (91, false, true), (30, false, true), (90, false, true)],
  some (some (88, false, true))),
 ([(3, true, true), (89, false, true), (91, false, true), (30, false, true), (90, true, false)],
  some (some (92, false, true))),
 ([(3, true, true), (89, false, true), (91, false, true), (30, true, false), (95, true, true)],
  some (some (88, false, true))),
 ([(3, true, true), (89, false, true), (91, false, true), (30, true, false), (95, false, false)],
  some (some (97, false, true))),
 ([(3, true, true), (89, false, true), (91, true, false), (30, false, true), (90, false, true)],
  some (some (99, false, true))),
 ([(3, true, true), (89, false, true), (91, true, false), (30, false, true), (90, true, false)],
  some (some (100, false, true))),
 ([(3, true, true), (89, false, true), (91, true, false), (30, true, false), (95, true, true)],
  some (some (99, false, true))),
 ([(3, true, true), (89, false, true), (91, true, false), (30, true, false), (95, false, false)],
  some (some (101, false, true))),
 ([(3, true, true), (89, true, false), (102, true, true), (30, false, true), (90, false, true)],
  some (some (88, false, true))),
 ([(3, true, true), (89, true, false), (102, true, true), (30, false, true), (90, true, false)],
  some (some (92, false, true))),
 ([(3, true, true), (89, true, false), (102, true, true), (30, true, false), (95, true, true)],
  some (some (88, false, true))),
 ([(3, true, true), (89, true, false), (102, true, true), (30, true, false), (95, false, false)],
  some (some (97, false, true))),
 ([(3, true, true), (89, true, false), (102, false, false), (30, false, true), (90, false, true)],
  some (some (104, false, true))),
 ([(3, true, true), (89, true, false), (102, false, false), (30, false, true), (90, true, false)],
  some (some (106, false, true))),
 ([(3, true, true), (89, true, false), (102, false, false), (30, true, false), (95, true, true)],
  some (some (104, false, true))),
 ([(3, true, true), (89, true, false), (102, false, false), (30, true, false), (95, false, false)],
  some (some (107, false, true)))]
private def goalCodes15_0_12 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(3, false, false), (10, false, false)], some (some (23, true, false))),
 ([(3, false, false), (10, true, true)], some (some (23, true, false))),
 ([(3, true, true), (30, false, false), (29, false, true), (10, false, false)], some (some (23, true, false))),
 ([(3, true, true), (30, false, false), (29, false, true), (10, true, true)], some (some (23, true, false))),
 ([(3, true, true), (30, false, false), (29, true, false), (10, false, false)], some (some (145, true, false))),
 ([(3, true, true), (30, false, false), (29, true, false), (10, true, true)], some (some (145, true, false))),
 ([(3, true, true), (30, true, true), (147, true, true), (10, false, false)], some (some (23, true, false))),
 ([(3, true, true), (30, true, true), (147, true, true), (10, true, true)], some (some (23, true, false))),
 ([(3, true, true), (30, true, true), (147, false, false), (10, false, false)], some (some (150, true, false))),
 ([(3, true, true), (30, true, true), (147, false, false), (10, true, true)], some (some (150, true, false)))]
private def goalCodes15_0_13 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(10, false, false), (8, false, false), (17, false, true)], some none),
 ([(10, false, false), (8, false, false), (17, true, false)], some none),
 ([(10, false, false), (8, true, true), (20, true, true)], some none),
 ([(10, false, false), (8, true, true), (20, false, false)], some none),
 ([(10, true, true), (18, false, false), (17, false, true), (8, false, false), (17, false, true)], some none),
 ([(10, true, true), (18, false, false), (17, false, true), (8, false, false), (17, true, false)], some none),
 ([(10, true, true), (18, false, false), (17, false, true), (8, true, true), (20, true, true)], some none),
 ([(10, true, true), (18, false, false), (17, false, true), (8, true, true), (20, false, false)], some none),
 ([(10, true, true), (18, false, false), (17, true, false), (8, false, false), (17, false, true)], none),
 ([(10, true, true), (18, false, false), (17, true, false), (8, false, false), (17, true, false)], some none),
 ([(10, true, true), (18, false, false), (17, true, false), (8, true, true), (20, true, true)], none),
 ([(10, true, true), (18, false, false), (17, true, false), (8, true, true), (20, false, false)],
  some (some (168, false, false))),
 ([(10, true, true), (18, true, true), (20, true, true), (8, false, false), (17, false, true)], some none),
 ([(10, true, true), (18, true, true), (20, true, true), (8, false, false), (17, true, false)], some none),
 ([(10, true, true), (18, true, true), (20, true, true), (8, true, true), (20, true, true)], some none),
 ([(10, true, true), (18, true, true), (20, true, true), (8, true, true), (20, false, false)], some none),
 ([(10, true, true), (18, true, true), (20, false, false), (8, false, false), (17, false, true)], none),
 ([(10, true, true), (18, true, true), (20, false, false), (8, false, false), (17, true, false)],
  some (some (168, true, false))),
 ([(10, true, true), (18, true, true), (20, false, false), (8, true, true), (20, true, true)], none),
 ([(10, true, true), (18, true, true), (20, false, false), (8, true, true), (20, false, false)], some none)]
private def goalCodes15_1_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([], none)]
private def goalCodes15_1_2 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(10, false, false), (4, false, false), (33, false, true)], some (some (36, true, true))),
 ([(10, false, false), (4, false, false), (33, true, false)], some (some (43, true, true))),
 ([(10, false, false), (4, true, true), (45, true, true)], some (some (36, true, true))),
 ([(10, false, false), (4, true, true), (45, false, false)], some (some (48, true, true)))]
private def goalCodes15_1_5 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(10, true, true), (50, false, true), (51, false, true), (18, false, true), (52, false, true)],
  some (some (53, false, true))),
 ([(10, true, true), (50, false, true), (51, false, true), (18, false, true), (52, true, false)],
  some (some (55, false, true))),
 ([(10, true, true), (50, false, true), (51, false, true), (18, true, false), (56, true, true)],
  some (some (53, false, true))),
 ([(10, true, true), (50, false, true), (51, false, true), (18, true, false), (56, false, false)],
  some (some (57, false, true))),
 ([(10, true, true), (50, false, true), (51, true, false), (18, false, true), (52, false, true)],
  some (some (59, false, true))),
 ([(10, true, true), (50, false, true), (51, true, false), (18, false, true), (52, true, false)],
  some (some (61, false, true))),
 ([(10, true, true), (50, false, true), (51, true, false), (18, true, false), (56, true, true)],
  some (some (59, false, true))),
 ([(10, true, true), (50, false, true), (51, true, false), (18, true, false), (56, false, false)],
  some (some (62, false, true))),
 ([(10, true, true), (50, true, false), (64, true, true), (18, false, true), (52, false, true)],
  some (some (53, false, true))),
 ([(10, true, true), (50, true, false), (64, true, true), (18, false, true), (52, true, false)],
  some (some (55, false, true))),
 ([(10, true, true), (50, true, false), (64, true, true), (18, true, false), (56, true, true)],
  some (some (53, false, true))),
 ([(10, true, true), (50, true, false), (64, true, true), (18, true, false), (56, false, false)],
  some (some (57, false, true))),
 ([(10, true, true), (50, true, false), (64, false, false), (18, false, true), (52, false, true)],
  some (some (65, false, true))),
 ([(10, true, true), (50, true, false), (64, false, false), (18, false, true), (52, true, false)],
  some (some (67, false, true))),
 ([(10, true, true), (50, true, false), (64, false, false), (18, true, false), (56, true, true)],
  some (some (65, false, true))),
 ([(10, true, true), (50, true, false), (64, false, false), (18, true, false), (56, false, false)],
  some (some (68, false, true)))]
private def goalCodes15_1_7 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(3, false, false), (6, false, false), (69, false, true)], some (some (73, true, true))),
 ([(3, false, false), (6, false, false), (69, true, false)], some (some (81, true, true))),
 ([(3, false, false), (6, true, true), (83, true, true)], some (some (73, true, true))),
 ([(3, false, false), (6, true, true), (83, false, false)], some (some (86, true, true)))]
private def goalCodes15_1_10 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(3, true, true), (89, false, true), (91, false, true), (30, false, true), (90, false, true)],
  some (some (88, false, true))),
 ([(3, true, true), (89, false, true), (91, false, true), (30, false, true), (90, true, false)],
  some (some (92, false, true))),
 ([(3, true, true), (89, false, true), (91, false, true), (30, true, false), (95, true, true)],
  some (some (88, false, true))),
 ([(3, true, true), (89, false, true), (91, false, true), (30, true, false), (95, false, false)],
  some (some (97, false, true))),
 ([(3, true, true), (89, false, true), (91, true, false), (30, false, true), (90, false, true)],
  some (some (99, false, true))),
 ([(3, true, true), (89, false, true), (91, true, false), (30, false, true), (90, true, false)],
  some (some (100, false, true))),
 ([(3, true, true), (89, false, true), (91, true, false), (30, true, false), (95, true, true)],
  some (some (99, false, true))),
 ([(3, true, true), (89, false, true), (91, true, false), (30, true, false), (95, false, false)],
  some (some (101, false, true))),
 ([(3, true, true), (89, true, false), (102, true, true), (30, false, true), (90, false, true)],
  some (some (88, false, true))),
 ([(3, true, true), (89, true, false), (102, true, true), (30, false, true), (90, true, false)],
  some (some (92, false, true))),
 ([(3, true, true), (89, true, false), (102, true, true), (30, true, false), (95, true, true)],
  some (some (88, false, true))),
 ([(3, true, true), (89, true, false), (102, true, true), (30, true, false), (95, false, false)],
  some (some (97, false, true))),
 ([(3, true, true), (89, true, false), (102, false, false), (30, false, true), (90, false, true)],
  some (some (104, false, true))),
 ([(3, true, true), (89, true, false), (102, false, false), (30, false, true), (90, true, false)],
  some (some (106, false, true))),
 ([(3, true, true), (89, true, false), (102, false, false), (30, true, false), (95, true, true)],
  some (some (104, false, true))),
 ([(3, true, true), (89, true, false), (102, false, false), (30, true, false), (95, false, false)],
  some (some (107, false, true)))]
private def goalCodes15_1_12 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(3, false, false), (10, false, false)], some (some (23, true, false))),
 ([(3, false, false), (10, true, true)], some (some (23, true, false))),
 ([(3, true, true), (30, false, false), (29, false, true), (10, false, false)], some (some (23, true, false))),
 ([(3, true, true), (30, false, false), (29, false, true), (10, true, true)], some (some (23, true, false))),
 ([(3, true, true), (30, false, false), (29, true, false), (10, false, false)], some (some (145, true, false))),
 ([(3, true, true), (30, false, false), (29, true, false), (10, true, true)], some (some (145, true, false))),
 ([(3, true, true), (30, true, true), (147, true, true), (10, false, false)], some (some (23, true, false))),
 ([(3, true, true), (30, true, true), (147, true, true), (10, true, true)], some (some (23, true, false))),
 ([(3, true, true), (30, true, true), (147, false, false), (10, false, false)], some (some (150, true, false))),
 ([(3, true, true), (30, true, true), (147, false, false), (10, true, true)], some (some (150, true, false)))]
private def goalCodes15_1_13 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(10, false, false), (8, false, false), (17, false, true)], some none),
 ([(10, false, false), (8, false, false), (17, true, false)], some none),
 ([(10, false, false), (8, true, true), (20, true, true)], some none),
 ([(10, false, false), (8, true, true), (20, false, false)], some none),
 ([(10, true, true), (18, false, false), (17, false, true), (8, false, false), (17, false, true)], some none),
 ([(10, true, true), (18, false, false), (17, false, true), (8, false, false), (17, true, false)], some none),
 ([(10, true, true), (18, false, false), (17, false, true), (8, true, true), (20, true, true)], some none),
 ([(10, true, true), (18, false, false), (17, false, true), (8, true, true), (20, false, false)], some none),
 ([(10, true, true), (18, false, false), (17, true, false), (8, false, false), (17, false, true)], none),
 ([(10, true, true), (18, false, false), (17, true, false), (8, false, false), (17, true, false)], some none),
 ([(10, true, true), (18, false, false), (17, true, false), (8, true, true), (20, true, true)], none),
 ([(10, true, true), (18, false, false), (17, true, false), (8, true, true), (20, false, false)],
  some (some (168, false, false))),
 ([(10, true, true), (18, true, true), (20, true, true), (8, false, false), (17, false, true)], some none),
 ([(10, true, true), (18, true, true), (20, true, true), (8, false, false), (17, true, false)], some none),
 ([(10, true, true), (18, true, true), (20, true, true), (8, true, true), (20, true, true)], some none),
 ([(10, true, true), (18, true, true), (20, true, true), (8, true, true), (20, false, false)], some none),
 ([(10, true, true), (18, true, true), (20, false, false), (8, false, false), (17, false, true)], none),
 ([(10, true, true), (18, true, true), (20, false, false), (8, false, false), (17, true, false)],
  some (some (168, true, false))),
 ([(10, true, true), (18, true, true), (20, false, false), (8, true, true), (20, true, true)], none),
 ([(10, true, true), (18, true, true), (20, false, false), (8, true, true), (20, false, false)], some none)]
private def goalCodes15_2_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([], none)]
private def goalCodes15_2_2 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(10, false, false), (4, false, false), (33, false, true)], some (some (36, true, true))),
 ([(10, false, false), (4, false, false), (33, true, false)], some (some (43, true, true))),
 ([(10, false, false), (4, true, true), (45, true, true)], some (some (36, true, true))),
 ([(10, false, false), (4, true, true), (45, false, false)], some (some (48, true, true)))]
private def goalCodes15_2_5 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(10, true, true), (50, false, true), (51, false, true), (18, false, true), (52, false, true)],
  some (some (53, false, true))),
 ([(10, true, true), (50, false, true), (51, false, true), (18, false, true), (52, true, false)],
  some (some (55, false, true))),
 ([(10, true, true), (50, false, true), (51, false, true), (18, true, false), (56, true, true)],
  some (some (53, false, true))),
 ([(10, true, true), (50, false, true), (51, false, true), (18, true, false), (56, false, false)],
  some (some (57, false, true))),
 ([(10, true, true), (50, false, true), (51, true, false), (18, false, true), (52, false, true)],
  some (some (59, false, true))),
 ([(10, true, true), (50, false, true), (51, true, false), (18, false, true), (52, true, false)],
  some (some (61, false, true))),
 ([(10, true, true), (50, false, true), (51, true, false), (18, true, false), (56, true, true)],
  some (some (59, false, true))),
 ([(10, true, true), (50, false, true), (51, true, false), (18, true, false), (56, false, false)],
  some (some (62, false, true))),
 ([(10, true, true), (50, true, false), (64, true, true), (18, false, true), (52, false, true)],
  some (some (53, false, true))),
 ([(10, true, true), (50, true, false), (64, true, true), (18, false, true), (52, true, false)],
  some (some (55, false, true))),
 ([(10, true, true), (50, true, false), (64, true, true), (18, true, false), (56, true, true)],
  some (some (53, false, true))),
 ([(10, true, true), (50, true, false), (64, true, true), (18, true, false), (56, false, false)],
  some (some (57, false, true))),
 ([(10, true, true), (50, true, false), (64, false, false), (18, false, true), (52, false, true)],
  some (some (65, false, true))),
 ([(10, true, true), (50, true, false), (64, false, false), (18, false, true), (52, true, false)],
  some (some (67, false, true))),
 ([(10, true, true), (50, true, false), (64, false, false), (18, true, false), (56, true, true)],
  some (some (65, false, true))),
 ([(10, true, true), (50, true, false), (64, false, false), (18, true, false), (56, false, false)],
  some (some (68, false, true)))]
private def goalCodes15_2_7 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(30, false, false), (297, false, false), (298, false, false), (69, false, true), (299, false, false)],
  some (some (300, true, true))),
 ([(30, false, false),
   (297, false, false),
   (298, false, false),
   (69, false, true),
   (299, true, true),
   (301, false, false),
   (303, false, true)],
  some (some (300, true, true))),
 ([(30, false, false),
   (297, false, false),
   (298, false, false),
   (69, false, true),
   (299, true, true),
   (301, false, false),
   (303, true, false)],
  some (some (304, true, true))),
 ([(30, false, false),
   (297, false, false),
   (298, false, false),
   (69, false, true),
   (299, true, true),
   (301, true, true),
   (307, true, true)],
  some (some (300, true, true))),
 ([(30, false, false),
   (297, false, false),
   (298, false, false),
   (69, false, true),
   (299, true, true),
   (301, true, true),
   (307, false, false)],
  some (some (309, true, true))),
 ([(30, false, false), (297, false, false), (298, false, false), (69, true, false), (299, false, false)],
  some (some (310, true, true))),
 ([(30, false, false),
   (297, false, false),
   (298, false, false),
   (69, true, false),
   (299, true, true),
   (301, false, false),
   (303, false, true)],
  some (some (310, true, true))),
 ([(30, false, false),
   (297, false, false),
   (298, false, false),
   (69, true, false),
   (299, true, true),
   (301, false, false),
   (303, true, false)],
  some (some (311, true, true))),
 ([(30, false, false),
   (297, false, false),
   (298, false, false),
   (69, true, false),
   (299, true, true),
   (301, true, true),
   (307, true, true)],
  some (some (310, true, true))),
 ([(30, false, false),
   (297, false, false),
   (298, false, false),
   (69, true, false),
   (299, true, true),
   (301, true, true),
   (307, false, false)],
  some (some (312, true, true))),
 ([(30, false, false), (297, false, false), (298, true, true), (83, true, true), (299, false, false)],
  some (some (300, true, true))),
 ([(30, false, false),
   (297, false, false),
   (298, true, true),
   (83, true, true),
   (299, true, true),
   (301, false, false),
   (303, false, true)],
  some (some (300, true, true))),
 ([(30, false, false),
   (297, false, false),
   (298, true, true),
   (83, true, true),
   (299, true, true),
   (301, false, false),
   (303, true, false)],
  some (some (304, true, true))),
 ([(30, false, false),
   (297, false, false),
   (298, true, true),
   (83, true, true),
   (299, true, true),
   (301, true, true),
   (307, true, true)],
  some (some (300, true, true))),
 ([(30, false, false),
   (297, false, false),
   (298, true, true),
   (83, true, true),
   (299, true, true),
   (301, true, true),
   (307, false, false)],
  some (some (309, true, true))),
 ([(30, false, false), (297, false, false), (298, true, true), (83, false, false), (299, false, false)],
  some (some (314, true, true))),
 ([(30, false, false),
   (297, false, false),
   (298, true, true),
   (83, false, false),
   (299, true, true),
   (301, false, false),
   (303, false, true)],
  some (some (314, true, true))),
 ([(30, false, false),
   (297, false, false),
   (298, true, true),
   (83, false, false),
   (299, true, true),
   (301, false, false),
   (303, true, false)],
  some (some (315, true, true))),
 ([(30, false, false),
   (297, false, false),
   (298, true, true),
   (83, false, false),
   (299, true, true),
   (301, true, true),
   (307, true, true)],
  some (some (314, true, true))),
 ([(30, false, false),
   (297, false, false),
   (298, true, true),
   (83, false, false),
   (299, true, true),
   (301, true, true),
   (307, false, false)],
  some (some (316, true, true))),
 ([(30, false, false), (297, true, true), (299, false, false)], some (some (300, true, true))),
 ([(30, false, false), (297, true, true), (299, true, true), (301, false, false), (303, false, true)],
  some (some (300, true, true))),
 ([(30, false, false), (297, true, true), (299, true, true), (301, false, false), (303, true, false)],
  some (some (304, true, true))),
 ([(30, false, false), (297, true, true), (299, true, true), (301, true, true), (307, true, true)],
  some (some (300, true, true))),
 ([(30, false, false), (297, true, true), (299, true, true), (301, true, true), (307, false, false)],
  some (some (309, true, true)))]
private def goalCodes15_2_9 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(30, true, true), (319, false, true), (320, false, true), (322, false, true), (321, false, true)],
  some (some (318, false, true))),
 ([(30, true, true), (319, false, true), (320, false, true), (322, false, true), (321, true, false)],
  some (some (323, false, true))),
 ([(30, true, true), (319, false, true), (320, false, true), (322, true, false), (325, true, true)],
  some (some (318, false, true))),
 ([(30, true, true), (319, false, true), (320, false, true), (322, true, false), (325, false, false)],
  some (some (327, false, true))),
 ([(30, true, true), (319, false, true), (320, true, false)], some (some (318, false, true))),
 ([(30, true, true),
   (319, true, false),
   (331, false, true),
   (332, false, true),
   (320, false, true),
   (322, false, true),
   (321, false, true)],
  some (some (318, false, true))),
 ([(30, true, true),
   (319, true, false),
   (331, false, true),
   (332, false, true),
   (320, false, true),
   (322, false, true),
   (321, true, false)],
  some (some (323, false, true))),
 ([(30, true, true),
   (319, true, false),
   (331, false, true),
   (332, false, true),
   (320, false, true),
   (322, true, false),
   (325, true, true)],
  some (some (318, false, true))),
 ([(30, true, true),
   (319, true, false),
   (331, false, true),
   (332, false, true),
   (320, false, true),
   (322, true, false),
   (325, false, false)],
  some (some (327, false, true))),
 ([(30, true, true), (319, true, false), (331, false, true), (332, false, true), (320, true, false)],
  some (some (318, false, true))),
 ([(30, true, true),
   (319, true, false),
   (331, false, true),
   (332, true, false),
   (320, false, true),
   (322, false, true),
   (321, false, true)],
  some (some (334, false, true))),
 ([(30, true, true),
   (319, true, false),
   (331, false, true),
   (332, true, false),
   (320, false, true),
   (322, false, true),
   (321, true, false)],
  some (some (335, false, true))),
 ([(30, true, true),
   (319, true, false),
   (331, false, true),
   (332, true, false),
   (320, false, true),
   (322, true, false),
   (325, true, true)],
  some (some (334, false, true))),
 ([(30, true, true),
   (319, true, false),
   (331, false, true),
   (332, true, false),
   (320, false, true),
   (322, true, false),
   (325, false, false)],
  some (some (336, false, true))),
 ([(30, true, true), (319, true, false), (331, false, true), (332, true, false), (320, true, false)],
  some (some (334, false, true))),
 ([(30, true, true),
   (319, true, false),
   (331, true, false),
   (337, true, true),
   (320, false, true),
   (322, false, true),
   (321, false, true)],
  some (some (318, false, true))),
 ([(30, true, true),
   (319, true, false),
   (331, true, false),
   (337, true, true),
   (320, false, true),
   (322, false, true),
   (321, true, false)],
  some (some (323, false, true))),
 ([(30, true, true),
   (319, true, false),
   (331, true, false),
   (337, true, true),
   (320, false, true),
   (322, true, false),
   (325, true, true)],
  some (some (318, false, true))),
 ([(30, true, true),
   (319, true, false),
   (331, true, false),
   (337, true, true),
   (320, false, true),
   (322, true, false),
   (325, false, false)],
  some (some (327, false, true))),
 ([(30, true, true), (319, true, false), (331, true, false), (337, true, true), (320, true, false)],
  some (some (318, false, true))),
 ([(30, true, true),
   (319, true, false),
   (331, true, false),
   (337, false, false),
   (320, false, true),
   (322, false, true),
   (321, false, true)],
  some (some (340, false, true))),
 ([(30, true, true),
   (319, true, false),
   (331, true, false),
   (337, false, false),
   (320, false, true),
   (322, false, true),
   (321, true, false)],
  some (some (341, false, true))),
 ([(30, true, true),
   (319, true, false),
   (331, true, false),
   (337, false, false),
   (320, false, true),
   (322, true, false),
   (325, true, true)],
  some (some (340, false, true))),
 ([(30, true, true),
   (319, true, false),
   (331, true, false),
   (337, false, false),
   (320, false, true),
   (322, true, false),
   (325, false, false)],
  some (some (342, false, true))),
 ([(30, true, true), (319, true, false), (331, true, false), (337, false, false), (320, true, false)],
  some (some (340, false, true)))]
private def goalCodes15_2_12 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(89, false, false), (380, false, false), (379, false, false), (377, false, true), (381, false, false)],
  some (some (378, true, true))),
 ([(89, false, false),
   (380, false, false),
   (379, false, false),
   (377, false, true),
   (381, true, true),
   (384, false, false),
   (383, false, true)],
  some (some (378, true, true))),
 ([(89, false, false),
   (380, false, false),
   (379, false, false),
   (377, false, true),
   (381, true, true),
   (384, false, false),
   (383, true, false)],
  some (some (385, true, true))),
 ([(89, false, false),
   (380, false, false),
   (379, false, false),
   (377, false, true),
   (381, true, true),
   (384, true, true),
   (388, true, true)],
  some (some (378, true, true))),
 ([(89, false, false),
   (380, false, false),
   (379, false, false),
   (377, false, true),
   (381, true, true),
   (384, true, true),
   (388, false, false)],
  some (some (390, true, true))),
 ([(89, false, false), (380, false, false), (379, false, false), (377, true, false), (381, false, false)],
  some (some (391, true, true))),
 ([(89, false, false),
   (380, false, false),
   (379, false, false),
   (377, true, false),
   (381, true, true),
   (384, false, false),
   (383, false, true)],
  some (some (391, true, true))),
 ([(89, false, false),
   (380, false, false),
   (379, false, false),
   (377, true, false),
   (381, true, true),
   (384, false, false),
   (383, true, false)],
  some (some (393, true, true))),
 ([(89, false, false),
   (380, false, false),
   (379, false, false),
   (377, true, false),
   (381, true, true),
   (384, true, true),
   (388, true, true)],
  some (some (391, true, true))),
 ([(89, false, false),
   (380, false, false),
   (379, false, false),
   (377, true, false),
   (381, true, true),
   (384, true, true),
   (388, false, false)],
  some (some (394, true, true))),
 ([(89, false, false), (380, false, false), (379, true, true), (395, true, true), (381, false, false)],
  some (some (378, true, true))),
 ([(89, false, false),
   (380, false, false),
   (379, true, true),
   (395, true, true),
   (381, true, true),
   (384, false, false),
   (383, false, true)],
  some (some (378, true, true))),
 ([(89, false, false),
   (380, false, false),
   (379, true, true),
   (395, true, true),
   (381, true, true),
   (384, false, false),
   (383, true, false)],
  some (some (385, true, true))),
 ([(89, false, false),
   (380, false, false),
   (379, true, true),
   (395, true, true),
   (381, true, true),
   (384, true, true),
   (388, true, true)],
  some (some (378, true, true))),
 ([(89, false, false),
   (380, false, false),
   (379, true, true),
   (395, true, true),
   (381, true, true),
   (384, true, true),
   (388, false, false)],
  some (some (390, true, true))),
 ([(89, false, false), (380, false, false), (379, true, true), (395, false, false), (381, false, false)],
  some (some (398, true, true))),
 ([(89, false, false),
   (380, false, false),
   (379, true, true),
   (395, false, false),
   (381, true, true),
   (384, false, false),
   (383, false, true)],
  some (some (398, true, true))),
 ([(89, false, false),
   (380, false, false),
   (379, true, true),
   (395, false, false),
   (381, true, true),
   (384, false, false),
   (383, true, false)],
  some (some (399, true, true))),
 ([(89, false, false),
   (380, false, false),
   (379, true, true),
   (395, false, false),
   (381, true, true),
   (384, true, true),
   (388, true, true)],
  some (some (398, true, true))),
 ([(89, false, false),
   (380, false, false),
   (379, true, true),
   (395, false, false),
   (381, true, true),
   (384, true, true),
   (388, false, false)],
  some (some (400, true, true))),
 ([(89, false, false), (380, true, true), (381, false, false)], some (some (378, true, true))),
 ([(89, false, false), (380, true, true), (381, true, true), (384, false, false), (383, false, true)],
  some (some (378, true, true))),
 ([(89, false, false), (380, true, true), (381, true, true), (384, false, false), (383, true, false)],
  some (some (385, true, true))),
 ([(89, false, false), (380, true, true), (381, true, true), (384, true, true), (388, true, true)],
  some (some (378, true, true))),
 ([(89, false, false), (380, true, true), (381, true, true), (384, true, true), (388, false, false)],
  some (some (390, true, true)))]
private def goalCodes15_2_14 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(89, true, true), (405, false, true), (404, false, true), (406, false, true), (403, false, true)],
  some (some (402, false, true))),
 ([(89, true, true), (405, false, true), (404, false, true), (406, false, true), (403, true, false)],
  some (some (407, false, true))),
 ([(89, true, true), (405, false, true), (404, false, true), (406, true, false), (409, true, true)],
  some (some (402, false, true))),
 ([(89, true, true), (405, false, true), (404, false, true), (406, true, false), (409, false, false)],
  some (some (411, false, true))),
 ([(89, true, true), (405, false, true), (404, true, false)], some (some (402, false, true))),
 ([(89, true, true),
   (405, true, false),
   (415, false, true),
   (414, false, true),
   (404, false, true),
   (406, false, true),
   (403, false, true)],
  some (some (402, false, true))),
 ([(89, true, true),
   (405, true, false),
   (415, false, true),
   (414, false, true),
   (404, false, true),
   (406, false, true),
   (403, true, false)],
  some (some (407, false, true))),
 ([(89, true, true),
   (405, true, false),
   (415, false, true),
   (414, false, true),
   (404, false, true),
   (406, true, false),
   (409, true, true)],
  some (some (402, false, true))),
 ([(89, true, true),
   (405, true, false),
   (415, false, true),
   (414, false, true),
   (404, false, true),
   (406, true, false),
   (409, false, false)],
  some (some (411, false, true))),
 ([(89, true, true), (405, true, false), (415, false, true), (414, false, true), (404, true, false)],
  some (some (402, false, true))),
 ([(89, true, true),
   (405, true, false),
   (415, false, true),
   (414, true, false),
   (404, false, true),
   (406, false, true),
   (403, false, true)],
  some (some (418, false, true))),
 ([(89, true, true),
   (405, true, false),
   (415, false, true),
   (414, true, false),
   (404, false, true),
   (406, false, true),
   (403, true, false)],
  some (some (419, false, true))),
 ([(89, true, true),
   (405, true, false),
   (415, false, true),
   (414, true, false),
   (404, false, true),
   (406, true, false),
   (409, true, true)],
  some (some (418, false, true))),
 ([(89, true, true),
   (405, true, false),
   (415, false, true),
   (414, true, false),
   (404, false, true),
   (406, true, false),
   (409, false, false)],
  some (some (420, false, true))),
 ([(89, true, true), (405, true, false), (415, false, true), (414, true, false), (404, true, false)],
  some (some (418, false, true))),
 ([(89, true, true),
   (405, true, false),
   (415, true, false),
   (421, true, true),
   (404, false, true),
   (406, false, true),
   (403, false, true)],
  some (some (402, false, true))),
 ([(89, true, true),
   (405, true, false),
   (415, true, false),
   (421, true, true),
   (404, false, true),
   (406, false, true),
   (403, true, false)],
  some (some (407, false, true))),
 ([(89, true, true),
   (405, true, false),
   (415, true, false),
   (421, true, true),
   (404, false, true),
   (406, true, false),
   (409, true, true)],
  some (some (402, false, true))),
 ([(89, true, true),
   (405, true, false),
   (415, true, false),
   (421, true, true),
   (404, false, true),
   (406, true, false),
   (409, false, false)],
  some (some (411, false, true))),
 ([(89, true, true), (405, true, false), (415, true, false), (421, true, true), (404, true, false)],
  some (some (402, false, true))),
 ([(89, true, true),
   (405, true, false),
   (415, true, false),
   (421, false, false),
   (404, false, true),
   (406, false, true),
   (403, false, true)],
  some (some (424, false, true))),
 ([(89, true, true),
   (405, true, false),
   (415, true, false),
   (421, false, false),
   (404, false, true),
   (406, false, true),
   (403, true, false)],
  some (some (425, false, true))),
 ([(89, true, true),
   (405, true, false),
   (415, true, false),
   (421, false, false),
   (404, false, true),
   (406, true, false),
   (409, true, true)],
  some (some (424, false, true))),
 ([(89, true, true),
   (405, true, false),
   (415, true, false),
   (421, false, false),
   (404, false, true),
   (406, true, false),
   (409, false, false)],
  some (some (426, false, true))),
 ([(89, true, true), (405, true, false), (415, true, false), (421, false, false), (404, true, false)],
  some (some (424, false, true)))]
private def goalCodes15_2_17 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(431, false, false), (432, false, false), (430, false, false), (427, false, true), (428, false, false)],
  some (some (429, true, true))),
 ([(431, false, false), (432, false, false), (430, false, false), (427, false, true), (428, true, true)],
  some (some (429, true, true))),
 ([(431, false, false), (432, false, false), (430, false, false), (427, true, false), (428, false, false)],
  some (some (434, true, true))),
 ([(431, false, false), (432, false, false), (430, false, false), (427, true, false), (428, true, true)],
  some (some (434, true, true))),
 ([(431, false, false), (432, false, false), (430, true, true), (436, true, true), (428, false, false)],
  some (some (429, true, true))),
 ([(431, false, false), (432, false, false), (430, true, true), (436, true, true), (428, true, true)],
  some (some (429, true, true))),
 ([(431, false, false), (432, false, false), (430, true, true), (436, false, false), (428, false, false)],
  some (some (439, true, true))),
 ([(431, false, false), (432, false, false), (430, true, true), (436, false, false), (428, true, true)],
  some (some (439, true, true))),
 ([(431, false, false), (432, true, true), (428, false, false)], some (some (429, true, true))),
 ([(431, false, false), (432, true, true), (428, true, true)], some (some (429, true, true)))]
private def goalCodes15_2_19 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(431, true, true), (443, false, true), (446, false, true), (445, false, true), (444, false, true)],
  some (some (441, false, true))),
 ([(431, true, true), (443, false, true), (446, false, true), (445, false, true), (444, true, false)],
  some (some (447, false, true))),
 ([(431, true, true), (443, false, true), (446, false, true), (445, true, false), (449, true, true)],
  some (some (441, false, true))),
 ([(431, true, true), (443, false, true), (446, false, true), (445, true, false), (449, false, false)],
  some (some (451, false, true))),
 ([(431, true, true), (443, false, true), (446, true, false)], some (some (441, false, true))),
 ([(431, true, true),
   (443, true, false),
   (455, false, true),
   (456, false, true),
   (446, false, true),
   (445, false, true),
   (444, false, true)],
  some (some (441, false, true))),
 ([(431, true, true),
   (443, true, false),
   (455, false, true),
   (456, false, true),
   (446, false, true),
   (445, false, true),
   (444, true, false)],
  some (some (447, false, true))),
 ([(431, true, true),
   (443, true, false),
   (455, false, true),
   (456, false, true),
   (446, false, true),
   (445, true, false),
   (449, true, true)],
  some (some (441, false, true))),
 ([(431, true, true),
   (443, true, false),
   (455, false, true),
   (456, false, true),
   (446, false, true),
   (445, true, false),
   (449, false, false)],
  some (some (451, false, true))),
 ([(431, true, true), (443, true, false), (455, false, true), (456, false, true), (446, true, false)],
  some (some (441, false, true))),
 ([(431, true, true),
   (443, true, false),
   (455, false, true),
   (456, true, false),
   (446, false, true),
   (445, false, true),
   (444, false, true)],
  some (some (458, false, true))),
 ([(431, true, true),
   (443, true, false),
   (455, false, true),
   (456, true, false),
   (446, false, true),
   (445, false, true),
   (444, true, false)],
  some (some (459, false, true))),
 ([(431, true, true),
   (443, true, false),
   (455, false, true),
   (456, true, false),
   (446, false, true),
   (445, true, false),
   (449, true, true)],
  some (some (458, false, true))),
 ([(431, true, true),
   (443, true, false),
   (455, false, true),
   (456, true, false),
   (446, false, true),
   (445, true, false),
   (449, false, false)],
  some (some (460, false, true))),
 ([(431, true, true), (443, true, false), (455, false, true), (456, true, false), (446, true, false)],
  some (some (458, false, true))),
 ([(431, true, true),
   (443, true, false),
   (455, true, false),
   (461, true, true),
   (446, false, true),
   (445, false, true),
   (444, false, true)],
  some (some (441, false, true))),
 ([(431, true, true),
   (443, true, false),
   (455, true, false),
   (461, true, true),
   (446, false, true),
   (445, false, true),
   (444, true, false)],
  some (some (447, false, true))),
 ([(431, true, true),
   (443, true, false),
   (455, true, false),
   (461, true, true),
   (446, false, true),
   (445, true, false),
   (449, true, true)],
  some (some (441, false, true))),
 ([(431, true, true),
   (443, true, false),
   (455, true, false),
   (461, true, true),
   (446, false, true),
   (445, true, false),
   (449, false, false)],
  some (some (451, false, true))),
 ([(431, true, true), (443, true, false), (455, true, false), (461, true, true), (446, true, false)],
  some (some (441, false, true))),
 ([(431, true, true),
   (443, true, false),
   (455, true, false),
   (461, false, false),
   (446, false, true),
   (445, false, true),
   (444, false, true)],
  some (some (464, false, true))),
 ([(431, true, true),
   (443, true, false),
   (455, true, false),
   (461, false, false),
   (446, false, true),
   (445, false, true),
   (444, true, false)],
  some (some (465, false, true))),
 ([(431, true, true),
   (443, true, false),
   (455, true, false),
   (461, false, false),
   (446, false, true),
   (445, true, false),
   (449, true, true)],
  some (some (464, false, true))),
 ([(431, true, true),
   (443, true, false),
   (455, true, false),
   (461, false, false),
   (446, false, true),
   (445, true, false),
   (449, false, false)],
  some (some (466, false, true))),
 ([(431, true, true), (443, true, false), (455, true, false), (461, false, false), (446, true, false)],
  some (some (464, false, true)))]
private def goalCodes15_2_22 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(30, false, false), (29, false, true), (10, false, false)], some (some (23, true, false))),
 ([(30, false, false), (29, false, true), (10, true, true)], some (some (23, true, false))),
 ([(30, false, false), (29, true, false), (10, false, false)], some (some (145, true, false))),
 ([(30, false, false), (29, true, false), (10, true, true)], some (some (145, true, false))),
 ([(30, true, true), (147, true, true), (10, false, false)], some (some (23, true, false))),
 ([(30, true, true), (147, true, true), (10, true, true)], some (some (23, true, false))),
 ([(30, true, true), (147, false, false), (10, false, false)], some (some (150, true, false))),
 ([(30, true, true), (147, false, false), (10, true, true)], some (some (150, true, false)))]
private def goalCodes15_2_24 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(431, false, false), (490, false, true), (89, false, false), (476, false, true)], some (some (489, false, false))),
 ([(431, false, false), (490, false, true), (89, false, false), (476, true, false)], some (some (491, false, false))),
 ([(431, false, false), (490, false, true), (89, true, true), (479, true, true)], some (some (489, false, false))),
 ([(431, false, false), (490, false, true), (89, true, true), (479, false, false)], some (some (492, false, false))),
 ([(431, false, false), (490, true, false), (89, false, false), (476, false, true)], some (some (494, false, false))),
 ([(431, false, false), (490, true, false), (89, false, false), (476, true, false)], some (some (495, false, false))),
 ([(431, false, false), (490, true, false), (89, true, true), (479, true, true)], some (some (494, false, false))),
 ([(431, false, false), (490, true, false), (89, true, true), (479, false, false)], some (some (496, false, false))),
 ([(431, true, true), (497, true, true), (89, false, false), (476, false, true)], some (some (489, false, false))),
 ([(431, true, true), (497, true, true), (89, false, false), (476, true, false)], some (some (491, false, false))),
 ([(431, true, true), (497, true, true), (89, true, true), (479, true, true)], some (some (489, false, false))),
 ([(431, true, true), (497, true, true), (89, true, true), (479, false, false)], some (some (492, false, false))),
 ([(431, true, true), (497, false, false), (89, false, false), (476, false, true)], some (some (499, false, false))),
 ([(431, true, true), (497, false, false), (89, false, false), (476, true, false)], some (some (500, false, false))),
 ([(431, true, true), (497, false, false), (89, true, true), (479, true, true)], some (some (499, false, false))),
 ([(431, true, true), (497, false, false), (89, true, true), (479, false, false)], some (some (501, false, false)))]
private def goalCodes15_2_25 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(10, false, false), (8, false, false), (17, false, true)], some none),
 ([(10, false, false), (8, false, false), (17, true, false)], some none),
 ([(10, false, false), (8, true, true), (20, true, true)], some none),
 ([(10, false, false), (8, true, true), (20, false, false)], some none),
 ([(10, true, true), (18, false, false), (17, false, true), (8, false, false), (17, false, true)], some none),
 ([(10, true, true), (18, false, false), (17, false, true), (8, false, false), (17, true, false)], some none),
 ([(10, true, true), (18, false, false), (17, false, true), (8, true, true), (20, true, true)], some none),
 ([(10, true, true), (18, false, false), (17, false, true), (8, true, true), (20, false, false)], some none),
 ([(10, true, true), (18, false, false), (17, true, false), (8, false, false), (17, false, true)], none),
 ([(10, true, true), (18, false, false), (17, true, false), (8, false, false), (17, true, false)], some none),
 ([(10, true, true), (18, false, false), (17, true, false), (8, true, true), (20, true, true)], none),
 ([(10, true, true), (18, false, false), (17, true, false), (8, true, true), (20, false, false)],
  some (some (168, false, false))),
 ([(10, true, true), (18, true, true), (20, true, true), (8, false, false), (17, false, true)], some none),
 ([(10, true, true), (18, true, true), (20, true, true), (8, false, false), (17, true, false)], some none),
 ([(10, true, true), (18, true, true), (20, true, true), (8, true, true), (20, true, true)], some none),
 ([(10, true, true), (18, true, true), (20, true, true), (8, true, true), (20, false, false)], some none),
 ([(10, true, true), (18, true, true), (20, false, false), (8, false, false), (17, false, true)], none),
 ([(10, true, true), (18, true, true), (20, false, false), (8, false, false), (17, true, false)],
  some (some (168, true, false))),
 ([(10, true, true), (18, true, true), (20, false, false), (8, true, true), (20, true, true)], none),
 ([(10, true, true), (18, true, true), (20, false, false), (8, true, true), (20, false, false)], some none)]
private def cutCodes15_0 : List (ℕ × Bool × Bool) := [(7, false, true)]
private def cutCodes15_1 : List (ℕ × Bool × Bool) := [(7, true, false), (177, false, false)]
private def cutCodes15_2 : List (ℕ × Bool × Bool) := [(7, true, false), (177, true, true)]

private theorem hGoal15_0_0 : trunkGoalBranches (trunkCatalog.states 15) 0 0 = goalCodes15_0_0.map decodeGoalBranch := by
  decide +kernel

private theorem hGoal15_0_2 : trunkGoalBranches (trunkCatalog.states 15) 0 2 = goalCodes15_0_2.map decodeGoalBranch := by
  decide +kernel

private theorem hGoal15_0_5 : trunkGoalBranches (trunkCatalog.states 15) 0 5 = goalCodes15_0_5.map decodeGoalBranch := by
  decide +kernel

private theorem hGoal15_0_7 : trunkGoalBranches (trunkCatalog.states 15) 0 7 = goalCodes15_0_7.map decodeGoalBranch := by
  decide +kernel

private theorem hGoal15_0_10 : trunkGoalBranches (trunkCatalog.states 15) 0 10 = goalCodes15_0_10.map decodeGoalBranch := by
  decide +kernel

private theorem hGoal15_0_12 : trunkGoalBranches (trunkCatalog.states 15) 0 12 = goalCodes15_0_12.map decodeGoalBranch := by
  decide +kernel

private theorem hGoal15_0_13 : trunkGoalBranches (trunkCatalog.states 15) 0 13 = goalCodes15_0_13.map decodeGoalBranch := by
  decide +kernel

private theorem hGoal15_1_0 : trunkGoalBranches (trunkCatalog.states 15) 1 0 = goalCodes15_1_0.map decodeGoalBranch := by
  exact hGoal15_0_0

private theorem hGoal15_1_2 : trunkGoalBranches (trunkCatalog.states 15) 1 2 = goalCodes15_1_2.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 15) 1 2 = trunkGoalBranches (trunkCatalog.states 15) 0 2 := by
      apply congrArg (trunkBranches (trunkCatalog.states 15).context)
      decide +kernel
    exact he.trans hGoal15_0_2
  | decide +kernel

private theorem hGoal15_1_5 : trunkGoalBranches (trunkCatalog.states 15) 1 5 = goalCodes15_1_5.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 15) 1 5 = trunkGoalBranches (trunkCatalog.states 15) 0 5 := by
      apply congrArg (trunkBranches (trunkCatalog.states 15).context)
      decide +kernel
    exact he.trans hGoal15_0_5
  | decide +kernel

private theorem hGoal15_1_7 : trunkGoalBranches (trunkCatalog.states 15) 1 7 = goalCodes15_1_7.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 15) 1 7 = trunkGoalBranches (trunkCatalog.states 15) 0 7 := by
      apply congrArg (trunkBranches (trunkCatalog.states 15).context)
      decide +kernel
    exact he.trans hGoal15_0_7
  | decide +kernel

private theorem hGoal15_1_10 : trunkGoalBranches (trunkCatalog.states 15) 1 10 = goalCodes15_1_10.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 15) 1 10 = trunkGoalBranches (trunkCatalog.states 15) 0 10 := by
      apply congrArg (trunkBranches (trunkCatalog.states 15).context)
      decide +kernel
    exact he.trans hGoal15_0_10
  | decide +kernel

private theorem hGoal15_1_12 : trunkGoalBranches (trunkCatalog.states 15) 1 12 = goalCodes15_1_12.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 15) 1 12 = trunkGoalBranches (trunkCatalog.states 15) 0 12 := by
      apply congrArg (trunkBranches (trunkCatalog.states 15).context)
      decide +kernel
    exact he.trans hGoal15_0_12
  | decide +kernel

private theorem hGoal15_1_13 : trunkGoalBranches (trunkCatalog.states 15) 1 13 = goalCodes15_1_13.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 15) 1 13 = trunkGoalBranches (trunkCatalog.states 15) 0 13 := by
      apply congrArg (trunkBranches (trunkCatalog.states 15).context)
      decide +kernel
    exact he.trans hGoal15_0_13
  | decide +kernel

private theorem hGoal15_2_0 : trunkGoalBranches (trunkCatalog.states 15) 2 0 = goalCodes15_2_0.map decodeGoalBranch := by
  exact hGoal15_0_0

private theorem hGoal15_2_2 : trunkGoalBranches (trunkCatalog.states 15) 2 2 = goalCodes15_2_2.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 15) 2 2 = trunkGoalBranches (trunkCatalog.states 15) 0 2 := by
      apply congrArg (trunkBranches (trunkCatalog.states 15).context)
      decide +kernel
    exact he.trans hGoal15_0_2
  | decide +kernel

private theorem hGoal15_2_5 : trunkGoalBranches (trunkCatalog.states 15) 2 5 = goalCodes15_2_5.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 15) 2 5 = trunkGoalBranches (trunkCatalog.states 15) 0 5 := by
      apply congrArg (trunkBranches (trunkCatalog.states 15).context)
      decide +kernel
    exact he.trans hGoal15_0_5
  | decide +kernel

private theorem hGoal15_2_7 : trunkGoalBranches (trunkCatalog.states 15) 2 7 = goalCodes15_2_7.map decodeGoalBranch := by
  decide +kernel

private theorem hGoal15_2_9 : trunkGoalBranches (trunkCatalog.states 15) 2 9 = goalCodes15_2_9.map decodeGoalBranch := by
  decide +kernel

private theorem hGoal15_2_12 : trunkGoalBranches (trunkCatalog.states 15) 2 12 = goalCodes15_2_12.map decodeGoalBranch := by
  decide +kernel

private theorem hGoal15_2_14 : trunkGoalBranches (trunkCatalog.states 15) 2 14 = goalCodes15_2_14.map decodeGoalBranch := by
  decide +kernel

private theorem hGoal15_2_17 : trunkGoalBranches (trunkCatalog.states 15) 2 17 = goalCodes15_2_17.map decodeGoalBranch := by
  decide +kernel

private theorem hGoal15_2_19 : trunkGoalBranches (trunkCatalog.states 15) 2 19 = goalCodes15_2_19.map decodeGoalBranch := by
  decide +kernel

private theorem hGoal15_2_22 : trunkGoalBranches (trunkCatalog.states 15) 2 22 = goalCodes15_2_22.map decodeGoalBranch := by
  decide +kernel

private theorem hGoal15_2_24 : trunkGoalBranches (trunkCatalog.states 15) 2 24 = goalCodes15_2_24.map decodeGoalBranch := by
  decide +kernel

private theorem hGoal15_2_25 : trunkGoalBranches (trunkCatalog.states 15) 2 25 = goalCodes15_2_25.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 15) 2 25 = trunkGoalBranches (trunkCatalog.states 15) 0 13 := by
      apply congrArg (trunkBranches (trunkCatalog.states 15).context)
      decide +kernel
    exact he.trans hGoal15_0_13
  | decide +kernel

private theorem hCut15_0 : (trunkPlanAt (trunkCatalog.states 15) 0).cuts = cutCodes15_0.map decodeThresholdBound := by decide +kernel

private theorem hCut15_1 : (trunkPlanAt (trunkCatalog.states 15) 1).cuts = cutCodes15_1.map decodeThresholdBound := by decide +kernel

private theorem hCut15_2 : (trunkPlanAt (trunkCatalog.states 15) 2).cuts = cutCodes15_2.map decodeThresholdBound := by decide +kernel

private def codedGoals15 (pi goal : ℕ) : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) :=
  if pi = 0 ∧ goal = 0 then goalCodes15_0_0 else
  if pi = 0 ∧ goal = 2 then goalCodes15_0_2 else
  if pi = 0 ∧ goal = 5 then goalCodes15_0_5 else
  if pi = 0 ∧ goal = 7 then goalCodes15_0_7 else
  if pi = 0 ∧ goal = 10 then goalCodes15_0_10 else
  if pi = 0 ∧ goal = 12 then goalCodes15_0_12 else
  if pi = 0 ∧ goal = 13 then goalCodes15_0_13 else
  if pi = 1 ∧ goal = 0 then goalCodes15_1_0 else
  if pi = 1 ∧ goal = 2 then goalCodes15_1_2 else
  if pi = 1 ∧ goal = 5 then goalCodes15_1_5 else
  if pi = 1 ∧ goal = 7 then goalCodes15_1_7 else
  if pi = 1 ∧ goal = 10 then goalCodes15_1_10 else
  if pi = 1 ∧ goal = 12 then goalCodes15_1_12 else
  if pi = 1 ∧ goal = 13 then goalCodes15_1_13 else
  if pi = 2 ∧ goal = 0 then goalCodes15_2_0 else
  if pi = 2 ∧ goal = 2 then goalCodes15_2_2 else
  if pi = 2 ∧ goal = 5 then goalCodes15_2_5 else
  if pi = 2 ∧ goal = 7 then goalCodes15_2_7 else
  if pi = 2 ∧ goal = 9 then goalCodes15_2_9 else
  if pi = 2 ∧ goal = 12 then goalCodes15_2_12 else
  if pi = 2 ∧ goal = 14 then goalCodes15_2_14 else
  if pi = 2 ∧ goal = 17 then goalCodes15_2_17 else
  if pi = 2 ∧ goal = 19 then goalCodes15_2_19 else
  if pi = 2 ∧ goal = 22 then goalCodes15_2_22 else
  if pi = 2 ∧ goal = 24 then goalCodes15_2_24 else
  if pi = 2 ∧ goal = 25 then goalCodes15_2_25 else
  []

private def codedKeys15 : List (ℕ × ℕ) := [(0, 0), (0, 2), (0, 5), (0, 7), (0, 10), (0, 12), (0, 13), (1, 0), (1, 2), (1, 5), (1, 7), (1, 10), (1, 12), (1, 13), (2, 0), (2, 2), (2, 5), (2, 7), (2, 9), (2, 12), (2, 14), (2, 17), (2, 19), (2, 22), (2, 24), (2, 25)]

private theorem hCodedGoals15 (pi goal : ℕ) (hm : (pi,goal) ∈ codedKeys15) : trunkGoalBranches (trunkCatalog.states 15) pi goal = (codedGoals15 pi goal).map decodeGoalBranch := by
  unfold codedGoals15
  by_cases h0 : pi = 0 ∧ goal = 0
  · rw [if_pos h0]
    rcases h0 with ⟨rfl,rfl⟩
    exact hGoal15_0_0
  rw [if_neg h0]
  by_cases h1 : pi = 0 ∧ goal = 2
  · rw [if_pos h1]
    rcases h1 with ⟨rfl,rfl⟩
    exact hGoal15_0_2
  rw [if_neg h1]
  by_cases h2 : pi = 0 ∧ goal = 5
  · rw [if_pos h2]
    rcases h2 with ⟨rfl,rfl⟩
    exact hGoal15_0_5
  rw [if_neg h2]
  by_cases h3 : pi = 0 ∧ goal = 7
  · rw [if_pos h3]
    rcases h3 with ⟨rfl,rfl⟩
    exact hGoal15_0_7
  rw [if_neg h3]
  by_cases h4 : pi = 0 ∧ goal = 10
  · rw [if_pos h4]
    rcases h4 with ⟨rfl,rfl⟩
    exact hGoal15_0_10
  rw [if_neg h4]
  by_cases h5 : pi = 0 ∧ goal = 12
  · rw [if_pos h5]
    rcases h5 with ⟨rfl,rfl⟩
    exact hGoal15_0_12
  rw [if_neg h5]
  by_cases h6 : pi = 0 ∧ goal = 13
  · rw [if_pos h6]
    rcases h6 with ⟨rfl,rfl⟩
    exact hGoal15_0_13
  rw [if_neg h6]
  by_cases h7 : pi = 1 ∧ goal = 0
  · rw [if_pos h7]
    rcases h7 with ⟨rfl,rfl⟩
    exact hGoal15_1_0
  rw [if_neg h7]
  by_cases h8 : pi = 1 ∧ goal = 2
  · rw [if_pos h8]
    rcases h8 with ⟨rfl,rfl⟩
    exact hGoal15_1_2
  rw [if_neg h8]
  by_cases h9 : pi = 1 ∧ goal = 5
  · rw [if_pos h9]
    rcases h9 with ⟨rfl,rfl⟩
    exact hGoal15_1_5
  rw [if_neg h9]
  by_cases h10 : pi = 1 ∧ goal = 7
  · rw [if_pos h10]
    rcases h10 with ⟨rfl,rfl⟩
    exact hGoal15_1_7
  rw [if_neg h10]
  by_cases h11 : pi = 1 ∧ goal = 10
  · rw [if_pos h11]
    rcases h11 with ⟨rfl,rfl⟩
    exact hGoal15_1_10
  rw [if_neg h11]
  by_cases h12 : pi = 1 ∧ goal = 12
  · rw [if_pos h12]
    rcases h12 with ⟨rfl,rfl⟩
    exact hGoal15_1_12
  rw [if_neg h12]
  by_cases h13 : pi = 1 ∧ goal = 13
  · rw [if_pos h13]
    rcases h13 with ⟨rfl,rfl⟩
    exact hGoal15_1_13
  rw [if_neg h13]
  by_cases h14 : pi = 2 ∧ goal = 0
  · rw [if_pos h14]
    rcases h14 with ⟨rfl,rfl⟩
    exact hGoal15_2_0
  rw [if_neg h14]
  by_cases h15 : pi = 2 ∧ goal = 2
  · rw [if_pos h15]
    rcases h15 with ⟨rfl,rfl⟩
    exact hGoal15_2_2
  rw [if_neg h15]
  by_cases h16 : pi = 2 ∧ goal = 5
  · rw [if_pos h16]
    rcases h16 with ⟨rfl,rfl⟩
    exact hGoal15_2_5
  rw [if_neg h16]
  by_cases h17 : pi = 2 ∧ goal = 7
  · rw [if_pos h17]
    rcases h17 with ⟨rfl,rfl⟩
    exact hGoal15_2_7
  rw [if_neg h17]
  by_cases h18 : pi = 2 ∧ goal = 9
  · rw [if_pos h18]
    rcases h18 with ⟨rfl,rfl⟩
    exact hGoal15_2_9
  rw [if_neg h18]
  by_cases h19 : pi = 2 ∧ goal = 12
  · rw [if_pos h19]
    rcases h19 with ⟨rfl,rfl⟩
    exact hGoal15_2_12
  rw [if_neg h19]
  by_cases h20 : pi = 2 ∧ goal = 14
  · rw [if_pos h20]
    rcases h20 with ⟨rfl,rfl⟩
    exact hGoal15_2_14
  rw [if_neg h20]
  by_cases h21 : pi = 2 ∧ goal = 17
  · rw [if_pos h21]
    rcases h21 with ⟨rfl,rfl⟩
    exact hGoal15_2_17
  rw [if_neg h21]
  by_cases h22 : pi = 2 ∧ goal = 19
  · rw [if_pos h22]
    rcases h22 with ⟨rfl,rfl⟩
    exact hGoal15_2_19
  rw [if_neg h22]
  by_cases h23 : pi = 2 ∧ goal = 22
  · rw [if_pos h23]
    rcases h23 with ⟨rfl,rfl⟩
    exact hGoal15_2_22
  rw [if_neg h23]
  by_cases h24 : pi = 2 ∧ goal = 24
  · rw [if_pos h24]
    rcases h24 with ⟨rfl,rfl⟩
    exact hGoal15_2_24
  rw [if_neg h24]
  by_cases h25 : pi = 2 ∧ goal = 25
  · rw [if_pos h25]
    rcases h25 with ⟨rfl,rfl⟩
    exact hGoal15_2_25
  rw [if_neg h25]
  simp_all only [codedKeys15,List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq]

private def codedCuts15 (pi : ℕ) : List (ℕ × Bool × Bool) :=
  if pi = 0 then cutCodes15_0 else
  if pi = 1 then cutCodes15_1 else
  if pi = 2 then cutCodes15_2 else
  []

private theorem hCodedCuts15 (pi goal : ℕ) (hm : (pi,goal) ∈ codedKeys15) : (trunkPlanAt (trunkCatalog.states 15) pi).cuts = (codedCuts15 pi).map decodeThresholdBound := by
  unfold codedCuts15
  by_cases h0 : pi = 0
  · rw [if_pos h0]
    subst pi
    exact hCut15_0
  rw [if_neg h0]
  by_cases h1 : pi = 1
  · rw [if_pos h1]
    subst pi
    exact hCut15_1
  rw [if_neg h1]
  by_cases h2 : pi = 2
  · rw [if_pos h2]
    subst pi
    exact hCut15_2
  rw [if_neg h2]
  simp_all only [codedKeys15,List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq,false_and]

private def codedValid15 (g : TrunkGroup) : Prop := (g.plan,g.goal) ∈ codedKeys15 ∧ codeGroupValid (trunkCatalog.states 15) codedParents15 codedCuts15 codedGoals15 g

private theorem codedValid15_sound (g : TrunkGroup) (h : codedValid15 g) : trunkGroupValidFast 15 g :=
  codeGroupValid_sound 15 codedParents15 codedCuts15 codedGoals15 g hCodedParents15 (hCodedCuts15 g.plan g.goal h.1) (hCodedGoals15 g.plan g.goal h.1) h.2



set_option Elab.async false
theorem batch_chunk_0 : ∀ j ∈ List.range 20, codedValid15 (trunkStateData15Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid15 codeGroupValid
  decide +kernel

theorem batch_chunk_20 : ∀ j ∈ List.range' 20 20, codedValid15 (trunkStateData15Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid15 codeGroupValid
  decide +kernel

theorem batch_chunk_40 : ∀ j ∈ List.range' 40 20, codedValid15 (trunkStateData15Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid15 codeGroupValid
  decide +kernel

theorem batch_chunk_60 : ∀ j ∈ List.range' 60 20, codedValid15 (trunkStateData15Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid15 codeGroupValid
  decide +kernel

theorem batch_chunk_80 : ∀ j ∈ List.range' 80 20, codedValid15 (trunkStateData15Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid15 codeGroupValid
  decide +kernel

theorem batch_key (j : ℕ) (hj : j < 100) : codedValid15 (trunkStateData15Part01.getD j ⟨0,[],0,[]⟩) := by
  rcases lt_or_ge j 20 with h0 | h0
  · exact batch_chunk_0 j (List.mem_range.2 (by omega))
  rcases lt_or_ge j 40 with h1 | h1
  · exact batch_chunk_20 j (List.mem_range'.2 ⟨j - 20, by omega, by omega⟩)
  rcases lt_or_ge j 60 with h2 | h2
  · exact batch_chunk_40 j (List.mem_range'.2 ⟨j - 40, by omega, by omega⟩)
  rcases lt_or_ge j 80 with h3 | h3
  · exact batch_chunk_60 j (List.mem_range'.2 ⟨j - 60, by omega, by omega⟩)
  · exact batch_chunk_80 j (List.mem_range'.2 ⟨j - 80, by omega, by omega⟩)

theorem part_length_1 : trunkStateData15Part01.length = 100 := by decide +kernel

theorem solution : trunkBindingBatch 15 0 100 := by
  intro i hlo hhi g hg
  change (trunkStateData15Part01 ++ trunkStateData15Part02)[i]? = some g at hg
  rw [List.getElem?_append_left (show i < (trunkStateData15Part01).length by simp only [List.length_append, part_length_1, Nat.reduceAdd]; omega)] at hg
  have hgi := batch_key (i - 0) (by omega)
  have hgv : trunkStateData15Part01.getD (i - 0) ⟨0,[],0,[]⟩ = g := by
    try simp only [Nat.sub_zero]
    rw [List.getD_eq_getElem?_getD, hg]; rfl
  rw [hgv] at hgi
  exact Freiman.trunkFast_correctness.2 15 hPar15 g (codedValid15_sound g hgi)

#print axioms solution
