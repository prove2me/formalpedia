-- Prove2me | solution 1 for Freiman.trunk_coverage_07
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:18:27.958477+00:00
-- url     : https://prove2.me/submissions/35811549-197e-43d4-b267-b6b6cd2dc77d

import Definitions.Def_Freiman_trunkGeometry
import Definitions.Def_Freiman_trunkFast
import Mathlib.Tactic
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def trunkRawParents (C : LowerHistoryContext) : List (List CertBound) :=
  let a := trunkBranches C ⟨([2],[]),true,([1],[]),false,false,[]⟩
  let b := trunkBranches C ⟨([1],[]),true,([2],[]),false,false,[]⟩
  a.flatMap fun (ca,ga) => b.filterMap fun (cb,gb) =>
    let base := ca++cb++[lowerHistoryHN,lowerHistoryZero]
    match ga,gb with
    | .impossible,_ | _,.impossible => none
    | .automatic,.automatic => some base
    | .bound g,.automatic | .automatic,.bound g => some (g::base)
    | .bound g,.bound h => some (g::h::base)

private theorem dedup_length (L acc : List (List CertBound)) :
    (L.foldl (fun acc bs => if acc.any (fun cs => decide (cs.toFinset = bs.toFinset))
      then acc else acc ++ [bs]) acc).length ≤ acc.length + L.length := by
  induction L generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    split
    · have ht := ih acc
      simp only [List.length_cons]
      omega
    · simpa only [List.length_cons, List.length_append, List.length_singleton, List.length_nil,
        Nat.add_assoc, Nat.add_comm 1] using ih (acc ++ [x])

private theorem parent_length (C : LowerHistoryContext) :
    (trunkParents C).length ≤ (trunkRawParents C).length := by
  change ((trunkRawParents C).foldl (fun acc bs => if acc.any (fun cs => decide (cs.toFinset = bs.toFinset))
    then acc else acc ++ [bs]) []).length ≤ _
  simpa using dedup_length (trunkRawParents C) []


private abbrev CoverageKey := ℕ × List ℕ × ℕ × List ℤ
private abbrev CoverageTask := ℕ × List (ℕ × List (ℕ × Bool))
private def coverageKeys (S : TrunkState) : List CoverageKey :=
  S.groups.map fun g => (g.plan, g.parents, g.goal, g.branches.map Prod.fst)
private def coverageTasks (S : TrunkState) : List CoverageTask :=
  (List.range (trunkSourcePlans S.context).length).map fun pi =>
    (pi, (List.range' 1 (trunkSpecs (trunkPlanAt S pi)).length).map fun goal =>
      (goal, (trunkGoalBranches S pi goal).zipIdx.map fun ba =>
        (ba.2, decide (ba.1.2 = LowerHistoryComparison.automatic))))
private def coverageKeyRecorded (keys : List CoverageKey) (plan parent goal : ℕ) (branch : ℤ) : Prop :=
  ∃ g ∈ keys, g.1 = plan ∧ parent ∈ g.2.1 ∧ g.2.2.1 = goal ∧ branch ∈ g.2.2.2
private theorem coverageKeyRecorded_sound (k : Fin 16) (plan parent goal : ℕ) (branch : ℤ)
    (h : coverageKeyRecorded (coverageKeys (trunkCatalog.states k)) plan parent goal branch) :
    trunkRecorded trunkCatalog k plan parent goal branch := by
  obtain ⟨key,hkey,hpi,hpar,hgoal,hbr⟩ := h
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hkey
  obtain ⟨⟨b,t⟩,hbt,hb⟩ := List.mem_map.mp hbr
  dsimp only at hb hpi hpar hgoal
  subst b
  exact ⟨g,hg,hpi,hpar,hgoal,t,hbt⟩
private def coverageTable (keys : List CoverageKey) (tasks : List CoverageTask) (parents : ℕ) : Prop :=
  ∀ pg ∈ tasks, ∀ par ∈ List.range parents,
    coverageKeyRecorded keys pg.1 par 0 (-1) ∨
    ∀ gb ∈ pg.2, ∀ ba ∈ gb.2,
      ba.2 = true ∨ coverageKeyRecorded keys pg.1 par gb.1 ba.1
private theorem coverageTable_sound (k : Fin 16)
    (hR : certRectangleValid (trunkCatalog.states k).rectangle)
    (h0 : 0 ≤ (trunkCatalog.states k).rectangle.r0)
    (h : coverageTable (coverageKeys (trunkCatalog.states k)) (coverageTasks (trunkCatalog.states k))
      (trunkRawParents (trunkCatalog.states k).context).length) : trunkCoverage trunkCatalog k := by
  refine ⟨hR,h0,?_⟩
  intro pi hpi par hpar
  have hp := lt_of_lt_of_le hpar (parent_length (trunkCatalog.states k).context)
  have htask := h _ (List.mem_map.mpr ⟨pi,List.mem_range.mpr hpi,rfl⟩) par (List.mem_range.mpr hp)
  rcases htask with he | hall
  · exact Or.inl (coverageKeyRecorded_sound _ _ _ _ _ he)
  · right
    intro goal hg hgl bi hbi
    have hgm : goal ∈ List.range' 1 (trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi)).length :=
      List.mem_range'.mpr ⟨goal-1, by omega, by omega⟩
    let bs := trunkGoalBranches (trunkCatalog.states k) pi goal
    have hget : bs[bi]? = some (bs[bi]'hbi) := List.getElem?_eq_getElem hbi
    have hm : (bs[bi]'hbi, bi) ∈ bs.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr hget
    have hb := hall _ (List.mem_map.mpr ⟨goal,hgm,rfl⟩) _ (List.mem_map.mpr ⟨(bs[bi]'hbi,bi),hm,rfl⟩)
    rcases hb with ha | hr
    · left
      have hat := of_decide_eq_true ha
      change ((bs[bi]?).getD ([], .impossible)).2 = _
      rw [hget]
      exact hat
    · exact Or.inr (coverageKeyRecorded_sound _ _ _ _ _ hr)

private def automaticFlags (C : LowerHistoryContext) (s : Section14Spec) : List Bool :=
  ((trunkEndpointCases C s.first s.firstUpper (trunkSpecIncoming s)).map Prod.fst).flatMap fun x =>
    ((trunkEndpointCases C s.second s.secondUpper (trunkSpecIncoming s)).map Prod.fst).map fun y =>
      decide (trunkGreater C x y s.strict = LowerHistoryComparison.automatic)
private theorem automaticFlags_eq (C : LowerHistoryContext) (s : Section14Spec) :
    automaticFlags C s = (trunkBranches C s).map (fun b => decide (b.2 = LowerHistoryComparison.automatic)) := by
  simp [automaticFlags, trunkBranches, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]

private def goalAutomaticFlags (S : TrunkState) (pi goal : ℕ) : List Bool :=
  if goal = 0 then [false] else
    automaticFlags S.context ((trunkSpecs (trunkPlanAt S pi))[goal-1]?.getD ⟨([],[]),false,([],[]),false,false,[]⟩)
private theorem goalAutomaticFlags_eq (S : TrunkState) (pi goal : ℕ) :
    goalAutomaticFlags S pi goal = (trunkGoalBranches S pi goal).map (fun b => decide (b.2 = LowerHistoryComparison.automatic)) := by
  by_cases h : goal = 0
  · simp [goalAutomaticFlags, trunkGoalBranches, h]
  · simp [goalAutomaticFlags, trunkGoalBranches, h, automaticFlags_eq]
private def coverageTasksProjection (S : TrunkState) : List CoverageTask :=
  (List.range (trunkSourcePlans S.context).length).map fun pi =>
    (pi, (List.range' 1 (trunkSpecs (trunkPlanAt S pi)).length).map fun goal =>
      (goal, (goalAutomaticFlags S pi goal).zipIdx.map Prod.swap))
private theorem coverageTasksProjection_eq (S : TrunkState) :
    coverageTasksProjection S = coverageTasks S := by
  simp [coverageTasksProjection, coverageTasks, goalAutomaticFlags_eq, List.zipIdx_map, List.map_map, Function.comp_def, Prod.map]



private def parentsFor (keys : List CoverageKey) (plan goal : ℕ) (branch : ℤ) : List ℕ :=
  keys.flatMap fun g => if g.1 = plan ∧ g.2.2.1 = goal ∧ branch ∈ g.2.2.2 then g.2.1 else []
private theorem parentsFor_sound (keys : List CoverageKey) (plan parent goal : ℕ) (branch : ℤ)
    (h : parent ∈ parentsFor keys plan goal branch) : coverageKeyRecorded keys plan parent goal branch := by
  obtain ⟨g,hg,hm⟩ := List.mem_flatMap.mp h
  split at hm
  next hc => exact ⟨g,hg,hc.1,hm,hc.2.1,hc.2.2⟩
  next hc => simp at hm

private def mergeFuel : ℕ → List ℕ → List ℕ → List ℕ
  | 0, xs, ys => xs ++ ys
  | _+1, [], ys => ys
  | _+1, xs, [] => xs
  | n+1, x::xs, y::ys => if x ≤ y then x :: mergeFuel n xs (y::ys) else y :: mergeFuel n (x::xs) ys
private theorem mem_mergeFuel (fuel : ℕ) (xs ys : List ℕ) (a : ℕ) :
    a ∈ mergeFuel fuel xs ys ↔ a ∈ xs ∨ a ∈ ys := by
  induction fuel generalizing xs ys with
  | zero => simp [mergeFuel]
  | succ n ih =>
    cases xs with
    | nil => simp [mergeFuel]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeFuel]
      | cons y ys =>
        simp only [mergeFuel]
        split
        · simp [ih, or_assoc]
        · simp [ih, or_assoc, or_left_comm, or_comm]
private def sortFuel : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | n+1, xs => if xs.length ≤ 1 then xs else
      mergeFuel xs.length (sortFuel n (xs.take (xs.length / 2))) (sortFuel n (xs.drop (xs.length / 2)))
private theorem mem_sortFuel (fuel : ℕ) (xs : List ℕ) (a : ℕ) :
    a ∈ sortFuel fuel xs ↔ a ∈ xs := by
  induction fuel generalizing xs with
  | zero => rfl
  | succ n ih =>
    simp only [sortFuel]
    split
    · rfl
    · rw [mem_mergeFuel, ih, ih, ← List.mem_append, List.take_append_drop]

private def coordinateFields7 : Array CertField := #[⟨(4/13),(1/13),(0/1),(0/1)⟩,⟨(1/2),(1/6),(0/1),(0/1)⟩,⟨(52/73),(1/73),(0/1),(0/1)⟩,⟨(89/214),(1/214),(0/1),(0/1)⟩,⟨(9/13),(-1/13),(0/1),(0/1)⟩,⟨(15/37),(-1/37),(0/1),(0/1)⟩,⟨(22/37),(1/37),(0/1),(0/1)⟩,⟨(113/179),(1/537),(0/1),(0/1)⟩,⟨(17/22),(-1/22),(0/1),(0/1)⟩,⟨(735/1006),(1/1006),(0/1),(0/1)⟩,⟨(66/179),(-1/537),(0/1),(0/1)⟩,⟨(125/214),(-1/214),(0/1),(0/1)⟩,⟨(35/94),(1/94),(0/1),(0/1)⟩,⟨(553/1429),(1/1429),(0/1),(0/1)⟩,⟨(10/23),(-1/69),(0/1),(0/1)⟩,⟨(1272/3013),(1/3013),(0/1),(0/1)⟩,⟨(5/22),(1/22),(0/1),(0/1)⟩,⟨(42/143),(1/429),(0/1),(0/1)⟩,⟨(271/1006),(-1/1006),(0/1),(0/1)⟩,⟨(16/59),(1/177),(0/1),(0/1)⟩,⟨(767/2749),(1/2749),(0/1),(0/1)⟩,⟨(43/142),(-1/142),(0/1),(0/1)⟩,⟨(1809/6094),(1/6094),(0/1),(0/1)⟩,⟨(2/1),(-1/1),(0/1),(0/1)⟩,⟨(731/2497),(-1/2497),(0/1),(0/1)⟩,⟨(517/1249),(-1/1249),(0/1),(0/1)⟩,⟨(101/143),(-1/429),(0/1),(0/1)⟩,⟨(13/23),(1/69),(0/1),(0/1)⟩,⟨(732/1249),(1/1249),(0/1),(0/1)⟩,⟨(59/94),(-1/94),(0/1),(0/1)⟩]
private abbrev coordinateInput7_0 : LowerPair × Bool × Bool := (([2], []), true, false)
private def coordinateCodes7_0 : List (ℕ × ℕ) := [(0, 1), (0, 1), (0, 2), (0, 1), (3, 1)]
private abbrev coordinateInput7_1 : LowerPair × Bool × Bool := (([1], []), false, false)
private def coordinateCodes7_1 : List (ℕ × ℕ) := [(4, 5), (4, 5)]
private abbrev coordinateInput7_2 : LowerPair × Bool × Bool := (([1], []), true, false)
private def coordinateCodes7_2 : List (ℕ × ℕ) := [(1, 1), (1, 1), (1, 2), (1, 1), (2, 1)]
private abbrev coordinateInput7_3 : LowerPair × Bool × Bool := (([2], []), false, false)
private def coordinateCodes7_3 : List (ℕ × ℕ) := [(5, 5), (5, 5)]
private abbrev coordinateInput7_4 : LowerPair × Bool × Bool := (([1, 1], []), true, false)
private def coordinateCodes7_4 : List (ℕ × ℕ) := [(6, 1), (6, 2), (6, 1), (7, 1)]
private abbrev coordinateInput7_5 : LowerPair × Bool × Bool := (([1, 2], []), false, false)
private def coordinateCodes7_5 : List (ℕ × ℕ) := [(8, 5)]
private abbrev coordinateInput7_6 : LowerPair × Bool × Bool := (([1, 2], []), true, false)
private def coordinateCodes7_6 : List (ℕ × ℕ) := [(2, 1), (2, 2), (2, 1), (9, 1)]
private abbrev coordinateInput7_7 : LowerPair × Bool × Bool := (([1, 1], []), false, false)
private def coordinateCodes7_7 : List (ℕ × ℕ) := [(4, 5)]
private abbrev coordinateInput7_8 : LowerPair × Bool × Bool := (([1], [1]), true, true)
private def coordinateCodes7_8 : List (ℕ × ℕ) := [(1, 1), (1, 2), (1, 1), (2, 1)]
private abbrev coordinateInput7_9 : LowerPair × Bool × Bool := (([1], [2]), false, true)
private def coordinateCodes7_9 : List (ℕ × ℕ) := [(4, 5), (4, 10), (4, 5), (11, 5)]
private abbrev coordinateInput7_10 : LowerPair × Bool × Bool := (([1], [2]), true, true)
private def coordinateCodes7_10 : List (ℕ × ℕ) := [(1, 0), (1, 3), (1, 0), (2, 0)]
private abbrev coordinateInput7_11 : LowerPair × Bool × Bool := (([1], [1]), false, true)
private def coordinateCodes7_11 : List (ℕ × ℕ) := [(4, 4), (4, 11), (4, 4), (11, 4)]
private abbrev coordinateInput7_12 : LowerPair × Bool × Bool := (([2, 1], []), true, false)
private def coordinateCodes7_12 : List (ℕ × ℕ) := [(12, 1), (12, 2), (12, 1), (13, 1)]
private abbrev coordinateInput7_13 : LowerPair × Bool × Bool := (([2, 2], []), false, false)
private def coordinateCodes7_13 : List (ℕ × ℕ) := [(14, 5)]
private abbrev coordinateInput7_14 : LowerPair × Bool × Bool := (([2, 2], []), true, false)
private def coordinateCodes7_14 : List (ℕ × ℕ) := [(3, 1), (3, 2), (3, 1), (15, 1)]
private abbrev coordinateInput7_15 : LowerPair × Bool × Bool := (([2, 1], []), false, false)
private def coordinateCodes7_15 : List (ℕ × ℕ) := [(5, 5)]
private abbrev coordinateInput7_16 : LowerPair × Bool × Bool := (([2], [1]), true, true)
private def coordinateCodes7_16 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 1), (3, 1)]
private abbrev coordinateInput7_17 : LowerPair × Bool × Bool := (([2], [2]), false, true)
private def coordinateCodes7_17 : List (ℕ × ℕ) := [(5, 5), (5, 10), (5, 5), (10, 5)]
private abbrev coordinateInput7_18 : LowerPair × Bool × Bool := (([2], [2]), true, true)
private def coordinateCodes7_18 : List (ℕ × ℕ) := [(0, 0), (0, 3), (0, 0), (3, 0)]
private abbrev coordinateInput7_19 : LowerPair × Bool × Bool := (([2], [1]), false, true)
private def coordinateCodes7_19 : List (ℕ × ℕ) := [(5, 4), (5, 11), (5, 4), (10, 4)]
private abbrev coordinateInput7_20 : LowerPair × Bool × Bool := (([3], []), true, false)
private def coordinateCodes7_20 : List (ℕ × ℕ) := [(16, 1), (16, 1), (16, 2), (16, 1), (17, 1)]
private abbrev coordinateInput7_21 : LowerPair × Bool × Bool := (([3], []), false, false)
private def coordinateCodes7_21 : List (ℕ × ℕ) := [(18, 5), (18, 5)]
private abbrev coordinateInput7_22 : LowerPair × Bool × Bool := (([3, 1], []), true, false)
private def coordinateCodes7_22 : List (ℕ × ℕ) := [(19, 1), (19, 2), (19, 1), (20, 1)]
private abbrev coordinateInput7_23 : LowerPair × Bool × Bool := (([3, 2], []), false, false)
private def coordinateCodes7_23 : List (ℕ × ℕ) := [(21, 5)]
private abbrev coordinateInput7_24 : LowerPair × Bool × Bool := (([3, 2], []), true, false)
private def coordinateCodes7_24 : List (ℕ × ℕ) := [(17, 1), (17, 2), (17, 1), (22, 1)]
private abbrev coordinateInput7_25 : LowerPair × Bool × Bool := (([3, 1], []), false, false)
private def coordinateCodes7_25 : List (ℕ × ℕ) := [(18, 5)]
private abbrev coordinateInput7_26 : LowerPair × Bool × Bool := (([3], [1]), true, true)
private def coordinateCodes7_26 : List (ℕ × ℕ) := [(16, 1), (16, 2), (16, 1), (17, 1)]
private abbrev coordinateInput7_27 : LowerPair × Bool × Bool := (([3], [2]), false, true)
private def coordinateCodes7_27 : List (ℕ × ℕ) := [(18, 5)]
private abbrev coordinateInput7_28 : LowerPair × Bool × Bool := (([3], [2]), true, true)
private def coordinateCodes7_28 : List (ℕ × ℕ) := [(16, 0), (16, 3), (16, 0), (17, 0)]
private abbrev coordinateInput7_29 : LowerPair × Bool × Bool := (([3], [1]), false, true)
private def coordinateCodes7_29 : List (ℕ × ℕ) := [(18, 4)]
private abbrev coordinateInput7_30 : LowerPair × Bool × Bool := (([], []), true, false)
private def coordinateCodes7_30 : List (ℕ × ℕ) := [(1, 1), (1, 2), (1, 1), (2, 1)]
private abbrev coordinateInput7_31 : LowerPair × Bool × Bool := (([], []), false, false)
private def coordinateCodes7_31 : List (ℕ × ℕ) := [(23, 5)]
private abbrev coordinateInput7_32 : LowerPair × Bool × Bool := (([3], [2]), true, false)
private def coordinateCodes7_32 : List (ℕ × ℕ) := [(16, 0), (16, 3), (16, 0), (17, 0)]
private abbrev coordinateInput7_33 : LowerPair × Bool × Bool := (([3], [2]), false, false)
private def coordinateCodes7_33 : List (ℕ × ℕ) := [(18, 5)]
private abbrev coordinateInput7_34 : LowerPair × Bool × Bool := (([3, 1], [2]), true, false)
private def coordinateCodes7_34 : List (ℕ × ℕ) := [(19, 0), (19, 3), (19, 0), (20, 0), (19, 0)]
private abbrev coordinateInput7_35 : LowerPair × Bool × Bool := (([3, 2], [2]), false, false)
private def coordinateCodes7_35 : List (ℕ × ℕ) := [(21, 5), (21, 5), (21, 10), (21, 5), (24, 5)]
private abbrev coordinateInput7_36 : LowerPair × Bool × Bool := (([3, 2], [2]), true, false)
private def coordinateCodes7_36 : List (ℕ × ℕ) := [(17, 0), (17, 3), (17, 0), (22, 0), (17, 0)]
private abbrev coordinateInput7_37 : LowerPair × Bool × Bool := (([3, 1], [2]), false, false)
private def coordinateCodes7_37 : List (ℕ × ℕ) := [(18, 5), (18, 5)]
private abbrev coordinateInput7_38 : LowerPair × Bool × Bool := (([3], [2, 1]), true, true)
private def coordinateCodes7_38 : List (ℕ × ℕ) := [(16, 12), (16, 12), (16, 13), (16, 12), (17, 12)]
private abbrev coordinateInput7_39 : LowerPair × Bool × Bool := (([3], [2, 2]), false, true)
private def coordinateCodes7_39 : List (ℕ × ℕ) := [(18, 14), (18, 14)]
private abbrev coordinateInput7_40 : LowerPair × Bool × Bool := (([3], [2, 2]), true, true)
private def coordinateCodes7_40 : List (ℕ × ℕ) := [(16, 3), (16, 3), (16, 15), (16, 3), (17, 3)]
private abbrev coordinateInput7_41 : LowerPair × Bool × Bool := (([3], [2, 1]), false, true)
private def coordinateCodes7_41 : List (ℕ × ℕ) := [(18, 5), (18, 5)]
private abbrev coordinateInput7_42 : LowerPair × Bool × Bool := (([2], [2]), true, false)
private def coordinateCodes7_42 : List (ℕ × ℕ) := [(0, 0), (0, 3), (0, 0), (3, 0)]
private abbrev coordinateInput7_43 : LowerPair × Bool × Bool := (([2], [2]), false, false)
private def coordinateCodes7_43 : List (ℕ × ℕ) := [(5, 5), (5, 10), (5, 5), (10, 5)]
private abbrev coordinateInput7_44 : LowerPair × Bool × Bool := (([2, 1], [2]), true, false)
private def coordinateCodes7_44 : List (ℕ × ℕ) := [(12, 0), (12, 3), (12, 0), (13, 0), (12, 0)]
private abbrev coordinateInput7_45 : LowerPair × Bool × Bool := (([2, 2], [2]), false, false)
private def coordinateCodes7_45 : List (ℕ × ℕ) := [(14, 5), (14, 5), (14, 10), (14, 5), (25, 5)]
private abbrev coordinateInput7_46 : LowerPair × Bool × Bool := (([2, 2], [2]), true, false)
private def coordinateCodes7_46 : List (ℕ × ℕ) := [(3, 0), (3, 3), (3, 0), (15, 0), (3, 0)]
private abbrev coordinateInput7_47 : LowerPair × Bool × Bool := (([2, 1], [2]), false, false)
private def coordinateCodes7_47 : List (ℕ × ℕ) := [(5, 5), (5, 5), (5, 10), (5, 5), (10, 5)]
private abbrev coordinateInput7_48 : LowerPair × Bool × Bool := (([2], [2, 1]), true, true)
private def coordinateCodes7_48 : List (ℕ × ℕ) := [(0, 12), (0, 12), (0, 13), (0, 12), (3, 12)]
private abbrev coordinateInput7_49 : LowerPair × Bool × Bool := (([2], [2, 2]), false, true)
private def coordinateCodes7_49 : List (ℕ × ℕ) := [(5, 14), (5, 25), (5, 14), (10, 14), (5, 14)]
private abbrev coordinateInput7_50 : LowerPair × Bool × Bool := (([2], [2, 2]), true, true)
private def coordinateCodes7_50 : List (ℕ × ℕ) := [(0, 3), (0, 3), (0, 15), (0, 3), (3, 3)]
private abbrev coordinateInput7_51 : LowerPair × Bool × Bool := (([2], [2, 1]), false, true)
private def coordinateCodes7_51 : List (ℕ × ℕ) := [(5, 5), (5, 10), (5, 5), (10, 5), (5, 5)]
private abbrev coordinateInput7_52 : LowerPair × Bool × Bool := (([2], [1]), true, false)
private def coordinateCodes7_52 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 1), (3, 1)]
private abbrev coordinateInput7_53 : LowerPair × Bool × Bool := (([2], [1]), false, false)
private def coordinateCodes7_53 : List (ℕ × ℕ) := [(5, 4), (5, 11), (5, 4), (10, 4)]
private abbrev coordinateInput7_54 : LowerPair × Bool × Bool := (([2, 1], [1]), true, false)
private def coordinateCodes7_54 : List (ℕ × ℕ) := [(12, 1), (12, 2), (12, 1), (13, 1), (12, 1)]
private abbrev coordinateInput7_55 : LowerPair × Bool × Bool := (([2, 2], [1]), false, false)
private def coordinateCodes7_55 : List (ℕ × ℕ) := [(14, 4), (14, 4), (14, 11), (14, 4), (25, 4)]
private abbrev coordinateInput7_56 : LowerPair × Bool × Bool := (([2, 2], [1]), true, false)
private def coordinateCodes7_56 : List (ℕ × ℕ) := [(3, 1), (3, 2), (3, 1), (15, 1), (3, 1)]
private abbrev coordinateInput7_57 : LowerPair × Bool × Bool := (([2, 1], [1]), false, false)
private def coordinateCodes7_57 : List (ℕ × ℕ) := [(5, 4), (5, 4), (5, 11), (5, 4), (10, 4)]
private abbrev coordinateInput7_58 : LowerPair × Bool × Bool := (([2], [1, 1]), true, true)
private def coordinateCodes7_58 : List (ℕ × ℕ) := [(0, 6), (0, 6), (0, 7), (0, 6), (3, 6)]
private abbrev coordinateInput7_59 : LowerPair × Bool × Bool := (([2], [1, 2]), false, true)
private def coordinateCodes7_59 : List (ℕ × ℕ) := [(5, 8), (5, 26), (5, 8), (10, 8), (5, 8)]
private abbrev coordinateInput7_60 : LowerPair × Bool × Bool := (([2], [1, 2]), true, true)
private def coordinateCodes7_60 : List (ℕ × ℕ) := [(0, 2), (0, 2), (0, 9), (0, 2), (3, 2)]
private abbrev coordinateInput7_61 : LowerPair × Bool × Bool := (([2], [1, 1]), false, true)
private def coordinateCodes7_61 : List (ℕ × ℕ) := [(5, 4), (5, 11), (5, 4), (10, 4), (5, 4)]
private abbrev coordinateInput7_62 : LowerPair × Bool × Bool := (([3], [1]), true, false)
private def coordinateCodes7_62 : List (ℕ × ℕ) := [(16, 1), (16, 2), (16, 1), (17, 1)]
private abbrev coordinateInput7_63 : LowerPair × Bool × Bool := (([3], [1]), false, false)
private def coordinateCodes7_63 : List (ℕ × ℕ) := [(18, 4)]
private abbrev coordinateInput7_64 : LowerPair × Bool × Bool := (([3, 1], [1]), true, false)
private def coordinateCodes7_64 : List (ℕ × ℕ) := [(19, 1), (19, 2), (19, 1), (20, 1), (19, 1)]
private abbrev coordinateInput7_65 : LowerPair × Bool × Bool := (([3, 2], [1]), false, false)
private def coordinateCodes7_65 : List (ℕ × ℕ) := [(21, 4), (21, 4), (21, 11), (21, 4), (24, 4)]
private abbrev coordinateInput7_66 : LowerPair × Bool × Bool := (([3, 2], [1]), true, false)
private def coordinateCodes7_66 : List (ℕ × ℕ) := [(17, 1), (17, 2), (17, 1), (22, 1), (17, 1)]
private abbrev coordinateInput7_67 : LowerPair × Bool × Bool := (([3, 1], [1]), false, false)
private def coordinateCodes7_67 : List (ℕ × ℕ) := [(18, 4), (18, 4)]
private abbrev coordinateInput7_68 : LowerPair × Bool × Bool := (([3], [1, 1]), true, true)
private def coordinateCodes7_68 : List (ℕ × ℕ) := [(16, 6), (16, 6), (16, 7), (16, 6), (17, 6)]
private abbrev coordinateInput7_69 : LowerPair × Bool × Bool := (([3], [1, 2]), false, true)
private def coordinateCodes7_69 : List (ℕ × ℕ) := [(18, 8), (18, 8)]
private abbrev coordinateInput7_70 : LowerPair × Bool × Bool := (([3], [1, 2]), true, true)
private def coordinateCodes7_70 : List (ℕ × ℕ) := [(16, 2), (16, 2), (16, 9), (16, 2), (17, 2)]
private abbrev coordinateInput7_71 : LowerPair × Bool × Bool := (([3], [1, 1]), false, true)
private def coordinateCodes7_71 : List (ℕ × ℕ) := [(18, 4), (18, 4)]
private abbrev coordinateInput7_72 : LowerPair × Bool × Bool := (([2], [3]), true, false)
private def coordinateCodes7_72 : List (ℕ × ℕ) := [(0, 16), (0, 17), (0, 16), (3, 16)]
private abbrev coordinateInput7_73 : LowerPair × Bool × Bool := (([2], [3]), false, false)
private def coordinateCodes7_73 : List (ℕ × ℕ) := [(5, 18)]
private abbrev coordinateInput7_74 : LowerPair × Bool × Bool := (([2, 1], [3]), true, false)
private def coordinateCodes7_74 : List (ℕ × ℕ) := [(12, 16), (12, 17), (12, 16), (13, 16), (12, 16)]
private abbrev coordinateInput7_75 : LowerPair × Bool × Bool := (([2, 2], [3]), false, false)
private def coordinateCodes7_75 : List (ℕ × ℕ) := [(14, 18), (14, 18)]
private abbrev coordinateInput7_76 : LowerPair × Bool × Bool := (([2, 2], [3]), true, false)
private def coordinateCodes7_76 : List (ℕ × ℕ) := [(3, 16), (3, 17), (3, 16), (15, 16), (3, 16)]
private abbrev coordinateInput7_77 : LowerPair × Bool × Bool := (([2, 1], [3]), false, false)
private def coordinateCodes7_77 : List (ℕ × ℕ) := [(5, 18), (5, 18)]
private abbrev coordinateInput7_78 : LowerPair × Bool × Bool := (([2], [3, 1]), true, true)
private def coordinateCodes7_78 : List (ℕ × ℕ) := [(0, 19), (0, 19), (0, 20), (0, 19), (3, 19)]
private abbrev coordinateInput7_79 : LowerPair × Bool × Bool := (([2], [3, 2]), false, true)
private def coordinateCodes7_79 : List (ℕ × ℕ) := [(5, 21), (5, 24), (5, 21), (10, 21), (5, 21)]
private abbrev coordinateInput7_80 : LowerPair × Bool × Bool := (([2], [3, 2]), true, true)
private def coordinateCodes7_80 : List (ℕ × ℕ) := [(0, 17), (0, 17), (0, 22), (0, 17), (3, 17)]
private abbrev coordinateInput7_81 : LowerPair × Bool × Bool := (([2], [3, 1]), false, true)
private def coordinateCodes7_81 : List (ℕ × ℕ) := [(5, 18), (5, 18)]
private abbrev coordinateInput7_82 : LowerPair × Bool × Bool := (([3], [1, 1]), true, false)
private def coordinateCodes7_82 : List (ℕ × ℕ) := [(16, 6), (16, 6), (16, 7), (16, 6), (17, 6)]
private abbrev coordinateInput7_83 : LowerPair × Bool × Bool := (([3], [1, 1]), false, false)
private def coordinateCodes7_83 : List (ℕ × ℕ) := [(18, 4), (18, 4)]
private abbrev coordinateInput7_84 : LowerPair × Bool × Bool := (([3, 1], [1, 1]), true, false)
private def coordinateCodes7_84 : List (ℕ × ℕ) := [(19, 6), (19, 7), (19, 6), (20, 6)]
private abbrev coordinateInput7_85 : LowerPair × Bool × Bool := (([3, 2], [1, 1]), false, false)
private def coordinateCodes7_85 : List (ℕ × ℕ) := [(21, 4), (21, 11), (21, 4), (24, 4)]
private abbrev coordinateInput7_86 : LowerPair × Bool × Bool := (([3, 2], [1, 1]), true, false)
private def coordinateCodes7_86 : List (ℕ × ℕ) := [(17, 6), (17, 7), (17, 6), (22, 6)]
private abbrev coordinateInput7_87 : LowerPair × Bool × Bool := (([3, 1], [1, 1]), false, false)
private def coordinateCodes7_87 : List (ℕ × ℕ) := [(18, 4)]
private abbrev coordinateInput7_88 : LowerPair × Bool × Bool := (([3], [1, 1, 1]), true, true)
private def coordinateCodes7_88 : List (ℕ × ℕ) := [(16, 6), (16, 7), (16, 6), (17, 6)]
private abbrev coordinateInput7_89 : LowerPair × Bool × Bool := (([3], [1, 1, 2]), false, true)
private def coordinateCodes7_89 : List (ℕ × ℕ) := [(18, 11)]
private abbrev coordinateInput7_90 : LowerPair × Bool × Bool := (([3], [1, 1, 2]), true, true)
private def coordinateCodes7_90 : List (ℕ × ℕ) := [(16, 27), (16, 28), (16, 27), (17, 27)]
private abbrev coordinateInput7_91 : LowerPair × Bool × Bool := (([3], [1, 1, 1]), false, true)
private def coordinateCodes7_91 : List (ℕ × ℕ) := [(18, 29)]

private def decodeCoordinate7 (x : ℕ × ℕ) : CertField × CertField :=
  (coordinateFields7[x.1]?.getD ⟨0,0,0,0⟩,coordinateFields7[x.2]?.getD ⟨0,0,0,0⟩)

private theorem hCoordinate7_0 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_0.1 coordinateInput7_0.2.1 coordinateInput7_0.2.2).map Prod.fst = coordinateCodes7_0.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_1 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_1.1 coordinateInput7_1.2.1 coordinateInput7_1.2.2).map Prod.fst = coordinateCodes7_1.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_2 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_2.1 coordinateInput7_2.2.1 coordinateInput7_2.2.2).map Prod.fst = coordinateCodes7_2.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_3 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_3.1 coordinateInput7_3.2.1 coordinateInput7_3.2.2).map Prod.fst = coordinateCodes7_3.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_4 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_4.1 coordinateInput7_4.2.1 coordinateInput7_4.2.2).map Prod.fst = coordinateCodes7_4.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_5 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_5.1 coordinateInput7_5.2.1 coordinateInput7_5.2.2).map Prod.fst = coordinateCodes7_5.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_6 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_6.1 coordinateInput7_6.2.1 coordinateInput7_6.2.2).map Prod.fst = coordinateCodes7_6.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_7 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_7.1 coordinateInput7_7.2.1 coordinateInput7_7.2.2).map Prod.fst = coordinateCodes7_7.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_8 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_8.1 coordinateInput7_8.2.1 coordinateInput7_8.2.2).map Prod.fst = coordinateCodes7_8.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_9 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_9.1 coordinateInput7_9.2.1 coordinateInput7_9.2.2).map Prod.fst = coordinateCodes7_9.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_10 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_10.1 coordinateInput7_10.2.1 coordinateInput7_10.2.2).map Prod.fst = coordinateCodes7_10.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_11 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_11.1 coordinateInput7_11.2.1 coordinateInput7_11.2.2).map Prod.fst = coordinateCodes7_11.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_12 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_12.1 coordinateInput7_12.2.1 coordinateInput7_12.2.2).map Prod.fst = coordinateCodes7_12.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_13 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_13.1 coordinateInput7_13.2.1 coordinateInput7_13.2.2).map Prod.fst = coordinateCodes7_13.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_14 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_14.1 coordinateInput7_14.2.1 coordinateInput7_14.2.2).map Prod.fst = coordinateCodes7_14.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_15 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_15.1 coordinateInput7_15.2.1 coordinateInput7_15.2.2).map Prod.fst = coordinateCodes7_15.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_16 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_16.1 coordinateInput7_16.2.1 coordinateInput7_16.2.2).map Prod.fst = coordinateCodes7_16.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_17 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_17.1 coordinateInput7_17.2.1 coordinateInput7_17.2.2).map Prod.fst = coordinateCodes7_17.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_18 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_18.1 coordinateInput7_18.2.1 coordinateInput7_18.2.2).map Prod.fst = coordinateCodes7_18.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_19 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_19.1 coordinateInput7_19.2.1 coordinateInput7_19.2.2).map Prod.fst = coordinateCodes7_19.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_20 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_20.1 coordinateInput7_20.2.1 coordinateInput7_20.2.2).map Prod.fst = coordinateCodes7_20.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_21 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_21.1 coordinateInput7_21.2.1 coordinateInput7_21.2.2).map Prod.fst = coordinateCodes7_21.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_22 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_22.1 coordinateInput7_22.2.1 coordinateInput7_22.2.2).map Prod.fst = coordinateCodes7_22.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_23 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_23.1 coordinateInput7_23.2.1 coordinateInput7_23.2.2).map Prod.fst = coordinateCodes7_23.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_24 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_24.1 coordinateInput7_24.2.1 coordinateInput7_24.2.2).map Prod.fst = coordinateCodes7_24.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_25 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_25.1 coordinateInput7_25.2.1 coordinateInput7_25.2.2).map Prod.fst = coordinateCodes7_25.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_26 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_26.1 coordinateInput7_26.2.1 coordinateInput7_26.2.2).map Prod.fst = coordinateCodes7_26.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_27 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_27.1 coordinateInput7_27.2.1 coordinateInput7_27.2.2).map Prod.fst = coordinateCodes7_27.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_28 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_28.1 coordinateInput7_28.2.1 coordinateInput7_28.2.2).map Prod.fst = coordinateCodes7_28.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_29 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_29.1 coordinateInput7_29.2.1 coordinateInput7_29.2.2).map Prod.fst = coordinateCodes7_29.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_30 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_30.1 coordinateInput7_30.2.1 coordinateInput7_30.2.2).map Prod.fst = coordinateCodes7_30.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_31 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_31.1 coordinateInput7_31.2.1 coordinateInput7_31.2.2).map Prod.fst = coordinateCodes7_31.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_32 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_32.1 coordinateInput7_32.2.1 coordinateInput7_32.2.2).map Prod.fst = coordinateCodes7_32.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_33 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_33.1 coordinateInput7_33.2.1 coordinateInput7_33.2.2).map Prod.fst = coordinateCodes7_33.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_34 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_34.1 coordinateInput7_34.2.1 coordinateInput7_34.2.2).map Prod.fst = coordinateCodes7_34.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_35 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_35.1 coordinateInput7_35.2.1 coordinateInput7_35.2.2).map Prod.fst = coordinateCodes7_35.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_36 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_36.1 coordinateInput7_36.2.1 coordinateInput7_36.2.2).map Prod.fst = coordinateCodes7_36.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_37 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_37.1 coordinateInput7_37.2.1 coordinateInput7_37.2.2).map Prod.fst = coordinateCodes7_37.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_38 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_38.1 coordinateInput7_38.2.1 coordinateInput7_38.2.2).map Prod.fst = coordinateCodes7_38.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_39 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_39.1 coordinateInput7_39.2.1 coordinateInput7_39.2.2).map Prod.fst = coordinateCodes7_39.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_40 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_40.1 coordinateInput7_40.2.1 coordinateInput7_40.2.2).map Prod.fst = coordinateCodes7_40.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_41 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_41.1 coordinateInput7_41.2.1 coordinateInput7_41.2.2).map Prod.fst = coordinateCodes7_41.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_42 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_42.1 coordinateInput7_42.2.1 coordinateInput7_42.2.2).map Prod.fst = coordinateCodes7_42.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_43 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_43.1 coordinateInput7_43.2.1 coordinateInput7_43.2.2).map Prod.fst = coordinateCodes7_43.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_44 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_44.1 coordinateInput7_44.2.1 coordinateInput7_44.2.2).map Prod.fst = coordinateCodes7_44.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_45 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_45.1 coordinateInput7_45.2.1 coordinateInput7_45.2.2).map Prod.fst = coordinateCodes7_45.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_46 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_46.1 coordinateInput7_46.2.1 coordinateInput7_46.2.2).map Prod.fst = coordinateCodes7_46.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_47 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_47.1 coordinateInput7_47.2.1 coordinateInput7_47.2.2).map Prod.fst = coordinateCodes7_47.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_48 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_48.1 coordinateInput7_48.2.1 coordinateInput7_48.2.2).map Prod.fst = coordinateCodes7_48.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_49 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_49.1 coordinateInput7_49.2.1 coordinateInput7_49.2.2).map Prod.fst = coordinateCodes7_49.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_50 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_50.1 coordinateInput7_50.2.1 coordinateInput7_50.2.2).map Prod.fst = coordinateCodes7_50.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_51 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_51.1 coordinateInput7_51.2.1 coordinateInput7_51.2.2).map Prod.fst = coordinateCodes7_51.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_52 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_52.1 coordinateInput7_52.2.1 coordinateInput7_52.2.2).map Prod.fst = coordinateCodes7_52.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_53 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_53.1 coordinateInput7_53.2.1 coordinateInput7_53.2.2).map Prod.fst = coordinateCodes7_53.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_54 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_54.1 coordinateInput7_54.2.1 coordinateInput7_54.2.2).map Prod.fst = coordinateCodes7_54.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_55 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_55.1 coordinateInput7_55.2.1 coordinateInput7_55.2.2).map Prod.fst = coordinateCodes7_55.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_56 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_56.1 coordinateInput7_56.2.1 coordinateInput7_56.2.2).map Prod.fst = coordinateCodes7_56.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_57 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_57.1 coordinateInput7_57.2.1 coordinateInput7_57.2.2).map Prod.fst = coordinateCodes7_57.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_58 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_58.1 coordinateInput7_58.2.1 coordinateInput7_58.2.2).map Prod.fst = coordinateCodes7_58.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_59 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_59.1 coordinateInput7_59.2.1 coordinateInput7_59.2.2).map Prod.fst = coordinateCodes7_59.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_60 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_60.1 coordinateInput7_60.2.1 coordinateInput7_60.2.2).map Prod.fst = coordinateCodes7_60.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_61 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_61.1 coordinateInput7_61.2.1 coordinateInput7_61.2.2).map Prod.fst = coordinateCodes7_61.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_62 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_62.1 coordinateInput7_62.2.1 coordinateInput7_62.2.2).map Prod.fst = coordinateCodes7_62.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_63 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_63.1 coordinateInput7_63.2.1 coordinateInput7_63.2.2).map Prod.fst = coordinateCodes7_63.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_64 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_64.1 coordinateInput7_64.2.1 coordinateInput7_64.2.2).map Prod.fst = coordinateCodes7_64.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_65 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_65.1 coordinateInput7_65.2.1 coordinateInput7_65.2.2).map Prod.fst = coordinateCodes7_65.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_66 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_66.1 coordinateInput7_66.2.1 coordinateInput7_66.2.2).map Prod.fst = coordinateCodes7_66.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_67 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_67.1 coordinateInput7_67.2.1 coordinateInput7_67.2.2).map Prod.fst = coordinateCodes7_67.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_68 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_68.1 coordinateInput7_68.2.1 coordinateInput7_68.2.2).map Prod.fst = coordinateCodes7_68.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_69 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_69.1 coordinateInput7_69.2.1 coordinateInput7_69.2.2).map Prod.fst = coordinateCodes7_69.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_70 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_70.1 coordinateInput7_70.2.1 coordinateInput7_70.2.2).map Prod.fst = coordinateCodes7_70.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_71 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_71.1 coordinateInput7_71.2.1 coordinateInput7_71.2.2).map Prod.fst = coordinateCodes7_71.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_72 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_72.1 coordinateInput7_72.2.1 coordinateInput7_72.2.2).map Prod.fst = coordinateCodes7_72.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_73 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_73.1 coordinateInput7_73.2.1 coordinateInput7_73.2.2).map Prod.fst = coordinateCodes7_73.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_74 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_74.1 coordinateInput7_74.2.1 coordinateInput7_74.2.2).map Prod.fst = coordinateCodes7_74.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_75 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_75.1 coordinateInput7_75.2.1 coordinateInput7_75.2.2).map Prod.fst = coordinateCodes7_75.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_76 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_76.1 coordinateInput7_76.2.1 coordinateInput7_76.2.2).map Prod.fst = coordinateCodes7_76.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_77 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_77.1 coordinateInput7_77.2.1 coordinateInput7_77.2.2).map Prod.fst = coordinateCodes7_77.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_78 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_78.1 coordinateInput7_78.2.1 coordinateInput7_78.2.2).map Prod.fst = coordinateCodes7_78.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_79 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_79.1 coordinateInput7_79.2.1 coordinateInput7_79.2.2).map Prod.fst = coordinateCodes7_79.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_80 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_80.1 coordinateInput7_80.2.1 coordinateInput7_80.2.2).map Prod.fst = coordinateCodes7_80.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_81 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_81.1 coordinateInput7_81.2.1 coordinateInput7_81.2.2).map Prod.fst = coordinateCodes7_81.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_82 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_82.1 coordinateInput7_82.2.1 coordinateInput7_82.2.2).map Prod.fst = coordinateCodes7_82.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_83 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_83.1 coordinateInput7_83.2.1 coordinateInput7_83.2.2).map Prod.fst = coordinateCodes7_83.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_84 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_84.1 coordinateInput7_84.2.1 coordinateInput7_84.2.2).map Prod.fst = coordinateCodes7_84.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_85 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_85.1 coordinateInput7_85.2.1 coordinateInput7_85.2.2).map Prod.fst = coordinateCodes7_85.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_86 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_86.1 coordinateInput7_86.2.1 coordinateInput7_86.2.2).map Prod.fst = coordinateCodes7_86.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_87 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_87.1 coordinateInput7_87.2.1 coordinateInput7_87.2.2).map Prod.fst = coordinateCodes7_87.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_88 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_88.1 coordinateInput7_88.2.1 coordinateInput7_88.2.2).map Prod.fst = coordinateCodes7_88.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_89 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_89.1 coordinateInput7_89.2.1 coordinateInput7_89.2.2).map Prod.fst = coordinateCodes7_89.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_90 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_90.1 coordinateInput7_90.2.1 coordinateInput7_90.2.2).map Prod.fst = coordinateCodes7_90.map decodeCoordinate7 := by decide +kernel

private theorem hCoordinate7_91 :
    (trunkEndpointCases (trunkCatalog.states 7).context coordinateInput7_91.1 coordinateInput7_91.2.1 coordinateInput7_91.2.2).map Prod.fst = coordinateCodes7_91.map decodeCoordinate7 := by decide +kernel

private def coverageRemainder (keys : List CoverageKey) (tasks : List CoverageTask)
    (parents : ℕ) (remainders : List (List ℕ)) : Prop :=
  ∀ pg ∈ tasks,
    (List.range parents).Sublist (sortFuel 12 (parentsFor keys pg.1 0 (-1) ++ remainders[pg.1]?.getD [])) ∧
    ∀ gb ∈ pg.2, ∀ ba ∈ gb.2,
      ba.2 = true ∨ (remainders[pg.1]?.getD []).Sublist
        (sortFuel 12 (parentsFor keys pg.1 gb.1 ba.1))
private theorem coverageRemainder_sound (keys : List CoverageKey) (tasks : List CoverageTask)
    (parents : ℕ) (remainders : List (List ℕ))
    (h : coverageRemainder keys tasks parents remainders) : coverageTable keys tasks parents := by
  intro pg hpg par hpar
  by_cases he : coverageKeyRecorded keys pg.1 par 0 (-1)
  · exact Or.inl he
  · right
    have hp : par ∈ remainders[pg.1]?.getD [] := by
      have hm : par ∈ parentsFor keys pg.1 0 (-1) ++ remainders[pg.1]?.getD [] := by
        simpa only [mem_sortFuel] using (h pg hpg).1.subset hpar
      rcases List.mem_append.mp hm with hx | hx
      · exact False.elim (he (parentsFor_sound _ _ _ _ _ hx))
      · exact hx
    intro gb hgb ba hba
    rcases (h pg hpg).2 gb hgb ba hba with ha | hs
    · exact Or.inl ha
    · right
      apply parentsFor_sound
      simpa only [mem_sortFuel] using hs.subset hp

private def checkedKeys : List CoverageKey := [(0,[0],0,[-1]),
(0,[1,13,15,17,19,20,32,34,36,38,40,52,54,56,58,60,72,74,76,78,80,92,94,96,98],0,[-1]),
(0,[2,3,4,5,6,7,8,9,10,11,22,23,24,25,26,27,28,29,30,31,42,43,44,45,46,47,48,49,50,51,62,63,64,65,66,67,68,69,70,71,82,83,84,85,86,87,88,89,90,91],0,[-1]),
(0,[12],0,[-1]),
(0,[14],0,[-1]),
(0,[16],0,[-1]),
(0,[18],0,[-1]),
(0,[21],2,[0,1,2,3]),
(0,[21,41],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[21,41],7,[0,1,2,3]),
(0,[21],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[21],12,[0,1,2,3]),
(0,[21],15,[0,1,2,3]),
(0,[21],17,[0,1,2,3,4,5,6,7,8,9]),
(0,[21],19,[0,1,2,3,4,5,6,7,8,9]),
(0,[21,41],20,[8,10,11,16,17,18]),
(0,[33],0,[-1]),
(0,[35],0,[-1]),
(0,[37],0,[-1]),
(0,[39],0,[-1]),
(0,[41],2,[0,1,2,3]),
(0,[41],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[41],12,[0,1,2,3]),
(0,[41],15,[0,1,2,3]),
(0,[41],17,[0,1,2,3,4,5,6,7,8,9]),
(0,[41],19,[0,1,2,3,4,5,6,7,8,9]),
(0,[53],0,[-1]),
(0,[55,75,95],0,[-1]),
(0,[57,77,97],0,[-1]),
(0,[59,79,99],0,[-1]),
(0,[61,73],0,[-1]),
(0,[81,93],0,[-1]),
(1,[0,12],0,[-1]),
(1,[1,13,15,17,19,20,32,34,36,38,40,52,54,56,58,60,72,74,76,78,80,92,94,96,98],0,[-1]),
(1,[2,3,4,5,6,7,8,9,10,11,22,23,24,25,26,27,28,29,30,31,42,43,44,45,46,47,48,49,50,51,62,63,64,65,66,67,68,69,70,71,82,83,84,85,86,87,88,89,90,91],0,[-1]),
(1,[14],0,[-1]),
(1,[16],0,[-1]),
(1,[18],0,[-1]),
(1,[21,33],0,[-1]),
(1,[35],0,[-1]),
(1,[37],0,[-1]),
(1,[39],0,[-1]),
(1,[41,61,81],0,[-1]),
(1,[53],0,[-1]),
(1,[55],0,[-1]),
(1,[57],0,[-1]),
(1,[59],0,[-1]),
(1,[73],0,[-1]),
(1,[75],0,[-1]),
(1,[77],0,[-1]),
(1,[79],0,[-1]),
(1,[93],0,[-1]),
(1,[95],0,[-1]),
(1,[97],0,[-1]),
(1,[99],0,[-1]),
(2,[0],0,[-1]),
(2,[1,13,15,17,19,20,32,34,36,38,40,52,54,56,58,60,72,74,76,78,80,92,94,96,98],0,[-1]),
(2,[2,3,4,5,6,7,8,9,10,11,22,23,24,25,26,27,28,29,30,31,42,43,44,45,46,47,48,49,50,51,62,63,64,65,66,67,68,69,70,71,82,83,84,85,86,87,88,89,90,91],0,[-1]),
(2,[12],0,[-1]),
(2,[14],0,[-1]),
(2,[16],0,[-1]),
(2,[18],0,[-1]),
(2,[21],0,[-1]),
(2,[33],0,[-1]),
(2,[35],0,[-1]),
(2,[37],0,[-1]),
(2,[39],0,[-1]),
(2,[41],2,[0,1,2,3]),
(2,[41],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[41,53,73,93],7,[0,1,2,3]),
(2,[41],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[41],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[41],14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[41],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[41],19,[0,1,2,3,4,5,6,7,8,9]),
(2,[41],22,[0,1,2,3,4,5,6,7,8,9]),
(2,[41],25,[8,10,11,16,17,18]),
(2,[53,73,93],2,[0,1,2,3]),
(2,[53],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[53],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[53],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[53],14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[53],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[53],19,[0,1,2,3,4,5,6,7,8,9]),
(2,[53],22,[0,1,2,3,4,5,6,7,8,9]),
(2,[53,73,93],25,[8,10,11,16,17,18]),
(2,[55],0,[-1]),
(2,[57],0,[-1]),
(2,[59],0,[-1]),
(2,[61],0,[-1]),
(2,[73],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[73],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[73],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[73],14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[73],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[73],19,[0,1,2,3,4,5,6,7,8,9]),
(2,[73],22,[0,1,2,3,4,5,6,7,8,9]),
(2,[75],0,[-1]),
(2,[77],0,[-1]),
(2,[79],0,[-1]),
(2,[81],0,[-1]),
(2,[93],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[93],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[93],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[93],14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[93],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[93],19,[0,1,2,3,4,5,6,7,8,9]),
(2,[93],22,[0,1,2,3,4,5,6,7,8,9]),
(2,[95],0,[-1]),
(2,[97],0,[-1]),
(2,[99],0,[-1]),
(3,[0,12],0,[-1]),
(3,[1,13,15,17,19,20,32,34,36,38,40,52,54,56,58,60,72,74,76,78,80,92,94,96,98],0,[-1]),
(3,[2,3,4,5,6,7,8,9,10,11,22,23,24,25,26,27,28,29,30,31,42,43,44,45,46,47,48,49,50,51,62,63,64,65,66,67,68,69,70,71,82,83,84,85,86,87,88,89,90,91],0,[-1]),
(3,[14],0,[-1]),
(3,[16],0,[-1]),
(3,[18],0,[-1]),
(3,[21,33],0,[-1]),
(3,[35],0,[-1]),
(3,[37],0,[-1]),
(3,[39],0,[-1]),
(3,[41,61,81],0,[-1]),
(3,[53],0,[-1]),
(3,[55],0,[-1]),
(3,[57],0,[-1]),
(3,[59],0,[-1]),
(3,[73,75],2,[0,1,2,3]),
(3,[73],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[73,75],7,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[73],9,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[73],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[73],14,[0,1,2,3,4,5,6,7,8,9]),
(3,[73],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[73],19,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[73],22,[0,1,2,3,4,5,6,7,8,9]),
(3,[73],24,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[73],27,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[73],29,[0,1,2,3,4,5,6,7,8,9]),
(3,[73,75],32,[0,1,2,3,4,5,6,7]),
(3,[73],34,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[73],35,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[73],36,[0,1,2,3]),
(3,[73],38,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[73],39,[0,1,2,3]),
(3,[73],40,[0,1,2,3]),
(3,[73],41,[8,10,11,16,17,18]),
(3,[75],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[75],9,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[75],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[75],14,[0,1,2,3,4,5,6,7,8,9]),
(3,[75],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[75],19,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[75],22,[0,1,2,3,4,5,6,7,8,9]),
(3,[75],24,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[75],27,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[75],29,[0,1,2,3,4,5,6,7,8,9]),
(3,[75],34,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[75],35,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[75],36,[0,1,2,3]),
(3,[75],38,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[75],39,[0,1,2,3]),
(3,[75],40,[0,1,2,3]),
(3,[75],41,[8,10,11,16,17,18]),
(3,[77],0,[-1]),
(3,[79],0,[-1]),
(3,[93],0,[-1]),
(3,[95],0,[-1]),
(3,[97],0,[-1]),
(3,[99],0,[-1]),
(4,[0,12,14],0,[-1]),
(4,[1,13,15,17,19,20,32,34,36,38,40,52,54,56,58,60,72,74,76,78,80,92,94,96,98],0,[-1]),
(4,[2,3,4,5,6,7,8,9,10,11,22,23,24,25,26,27,28,29,30,31,42,43,44,45,46,47,48,49,50,51,62,63,64,65,66,67,68,69,70,71,82,83,84,85,86,87,88,89,90,91],0,[-1]),
(4,[16],0,[-1]),
(4,[18],0,[-1]),
(4,[21,33,35],0,[-1]),
(4,[37],0,[-1]),
(4,[39],0,[-1]),
(4,[41,61,81],0,[-1]),
(4,[53,55],0,[-1]),
(4,[57],0,[-1]),
(4,[59],0,[-1]),
(4,[73],0,[-1]),
(4,[75],2,[0,1,2,3]),
(4,[75],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(4,[75],7,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[75],9,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[75],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(4,[75],15,[0,1,2,3]),
(4,[75],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[75],19,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[75],22,[0,1,2,3,4,5,6,7,8,9]),
(4,[75],24,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[75],27,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[75],29,[0,1,2,3,4,5,6,7,8,9]),
(4,[75],32,[0,1,2,3,4,5,6,7]),
(4,[75],34,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]),
(4,[75],35,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]),
(4,[75],36,[0,1,2,3,4,5,6,7]),
(4,[75],38,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(4,[75],39,[0,1,2,3]),
(4,[75],40,[0,1,2,3]),
(4,[75],41,[8,10,11,16,17,18]),
(4,[77],0,[-1]),
(4,[79],0,[-1]),
(4,[93,95],0,[-1]),
(4,[97],0,[-1]),
(4,[99],0,[-1])]
private def checkedTasks : List CoverageTask := [(0,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 16 true).zipIdx.map Prod.swap),(5, (List.replicate 16 false).zipIdx.map Prod.swap),(6, (List.replicate 10 true).zipIdx.map Prod.swap),(7, (List.replicate 4 false).zipIdx.map Prod.swap),(8, (List.replicate 4 true).zipIdx.map Prod.swap),(9, (List.replicate 16 true).zipIdx.map Prod.swap),(10, (List.replicate 16 false).zipIdx.map Prod.swap),(11, (List.replicate 10 true).zipIdx.map Prod.swap),(12, (List.replicate 4 false).zipIdx.map Prod.swap),(13, (List.replicate 4 true).zipIdx.map Prod.swap),(14, (List.replicate 4 true).zipIdx.map Prod.swap),(15, (List.replicate 4 false).zipIdx.map Prod.swap),(16, (List.replicate 10 true).zipIdx.map Prod.swap),(17, (List.replicate 10 false).zipIdx.map Prod.swap),(18, (List.replicate 10 true).zipIdx.map Prod.swap),(19, (List.replicate 10 false).zipIdx.map Prod.swap),(20, [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true].zipIdx.map Prod.swap),(21, (List.replicate 2 true).zipIdx.map Prod.swap)]),(1,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 16 true).zipIdx.map Prod.swap),(5, (List.replicate 16 false).zipIdx.map Prod.swap),(6, (List.replicate 10 true).zipIdx.map Prod.swap),(7, (List.replicate 4 false).zipIdx.map Prod.swap),(8, (List.replicate 4 true).zipIdx.map Prod.swap),(9, (List.replicate 16 true).zipIdx.map Prod.swap),(10, (List.replicate 16 false).zipIdx.map Prod.swap),(11, (List.replicate 4 true).zipIdx.map Prod.swap),(12, (List.replicate 25 false).zipIdx.map Prod.swap),(13, (List.replicate 10 true).zipIdx.map Prod.swap),(14, (List.replicate 10 false).zipIdx.map Prod.swap),(15, (List.replicate 10 true).zipIdx.map Prod.swap),(16, (List.replicate 10 true).zipIdx.map Prod.swap),(17, (List.replicate 10 false).zipIdx.map Prod.swap),(18, (List.replicate 5 true).zipIdx.map Prod.swap),(19, (List.replicate 8 false).zipIdx.map Prod.swap),(20, [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true].zipIdx.map Prod.swap),(21, (List.replicate 1 true).zipIdx.map Prod.swap)]),(2,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 16 true).zipIdx.map Prod.swap),(5, (List.replicate 16 false).zipIdx.map Prod.swap),(6, (List.replicate 10 true).zipIdx.map Prod.swap),(7, (List.replicate 4 false).zipIdx.map Prod.swap),(8, (List.replicate 4 true).zipIdx.map Prod.swap),(9, (List.replicate 16 true).zipIdx.map Prod.swap),(10, (List.replicate 16 false).zipIdx.map Prod.swap),(11, (List.replicate 16 true).zipIdx.map Prod.swap),(12, (List.replicate 25 false).zipIdx.map Prod.swap),(13, (List.replicate 25 true).zipIdx.map Prod.swap),(14, (List.replicate 25 false).zipIdx.map Prod.swap),(15, (List.replicate 25 true).zipIdx.map Prod.swap),(16, (List.replicate 4 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 10 true).zipIdx.map Prod.swap),(19, (List.replicate 10 false).zipIdx.map Prod.swap),(20, (List.replicate 10 true).zipIdx.map Prod.swap),(21, (List.replicate 10 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 20 true).zipIdx.map Prod.swap),(24, (List.replicate 8 true).zipIdx.map Prod.swap),(25, [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true].zipIdx.map Prod.swap),(26, (List.replicate 1 true).zipIdx.map Prod.swap)]),(3,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 16 true).zipIdx.map Prod.swap),(5, (List.replicate 16 false).zipIdx.map Prod.swap),(6, (List.replicate 16 true).zipIdx.map Prod.swap),(7, (List.replicate 25 false).zipIdx.map Prod.swap),(8, (List.replicate 25 true).zipIdx.map Prod.swap),(9, (List.replicate 25 false).zipIdx.map Prod.swap),(10, (List.replicate 25 true).zipIdx.map Prod.swap),(11, (List.replicate 4 true).zipIdx.map Prod.swap),(12, (List.replicate 25 false).zipIdx.map Prod.swap),(13, (List.replicate 10 true).zipIdx.map Prod.swap),(14, (List.replicate 10 false).zipIdx.map Prod.swap),(15, (List.replicate 10 true).zipIdx.map Prod.swap),(16, (List.replicate 16 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 25 true).zipIdx.map Prod.swap),(19, (List.replicate 25 false).zipIdx.map Prod.swap),(20, (List.replicate 25 true).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 25 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 4 true).zipIdx.map Prod.swap),(27, (List.replicate 25 false).zipIdx.map Prod.swap),(28, (List.replicate 10 true).zipIdx.map Prod.swap),(29, (List.replicate 10 false).zipIdx.map Prod.swap),(30, (List.replicate 10 true).zipIdx.map Prod.swap),(31, (List.replicate 20 true).zipIdx.map Prod.swap),(32, (List.replicate 8 false).zipIdx.map Prod.swap),(33, (List.replicate 4 true).zipIdx.map Prod.swap),(34, (List.replicate 16 false).zipIdx.map Prod.swap),(35, (List.replicate 16 false).zipIdx.map Prod.swap),(36, (List.replicate 4 false).zipIdx.map Prod.swap),(37, (List.replicate 4 true).zipIdx.map Prod.swap),(38, (List.replicate 16 false).zipIdx.map Prod.swap),(39, (List.replicate 4 false).zipIdx.map Prod.swap),(40, (List.replicate 4 false).zipIdx.map Prod.swap),(41, [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true].zipIdx.map Prod.swap),(42, (List.replicate 1 true).zipIdx.map Prod.swap)]),(4,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 16 true).zipIdx.map Prod.swap),(5, (List.replicate 16 false).zipIdx.map Prod.swap),(6, (List.replicate 16 true).zipIdx.map Prod.swap),(7, (List.replicate 25 false).zipIdx.map Prod.swap),(8, (List.replicate 25 true).zipIdx.map Prod.swap),(9, (List.replicate 25 false).zipIdx.map Prod.swap),(10, (List.replicate 25 true).zipIdx.map Prod.swap),(11, (List.replicate 10 true).zipIdx.map Prod.swap),(12, (List.replicate 16 false).zipIdx.map Prod.swap),(13, (List.replicate 4 true).zipIdx.map Prod.swap),(14, (List.replicate 4 true).zipIdx.map Prod.swap),(15, (List.replicate 4 false).zipIdx.map Prod.swap),(16, (List.replicate 16 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 25 true).zipIdx.map Prod.swap),(19, (List.replicate 25 false).zipIdx.map Prod.swap),(20, (List.replicate 25 true).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 25 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 4 true).zipIdx.map Prod.swap),(27, (List.replicate 25 false).zipIdx.map Prod.swap),(28, (List.replicate 10 true).zipIdx.map Prod.swap),(29, (List.replicate 10 false).zipIdx.map Prod.swap),(30, (List.replicate 10 true).zipIdx.map Prod.swap),(31, (List.replicate 20 true).zipIdx.map Prod.swap),(32, (List.replicate 8 false).zipIdx.map Prod.swap),(33, (List.replicate 8 true).zipIdx.map Prod.swap),(34, (List.replicate 20 false).zipIdx.map Prod.swap),(35, (List.replicate 20 false).zipIdx.map Prod.swap),(36, (List.replicate 8 false).zipIdx.map Prod.swap),(37, (List.replicate 4 true).zipIdx.map Prod.swap),(38, (List.replicate 16 false).zipIdx.map Prod.swap),(39, (List.replicate 4 false).zipIdx.map Prod.swap),(40, (List.replicate 4 false).zipIdx.map Prod.swap),(41, [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true].zipIdx.map Prod.swap),(42, (List.replicate 1 true).zipIdx.map Prod.swap)])]
private theorem automaticFlags_cached (C : LowerHistoryContext) (s : Section14Spec)
    (left right : LowerPair × Bool × Bool) (ls rs : List (CertField × CertField))
    (hl : (s.first, s.firstUpper, trunkSpecIncoming s) = left)
    (hr : (s.second, s.secondUpper, trunkSpecIncoming s) = right)
    (hLeft : (trunkEndpointCases C left.1 left.2.1 left.2.2).map Prod.fst = ls)
    (hRight : (trunkEndpointCases C right.1 right.2.1 right.2.2).map Prod.fst = rs) :
    automaticFlags C s = ls.flatMap (fun x => rs.map (fun y =>
      decide (trunkGreater C x y s.strict = LowerHistoryComparison.automatic))) := by
  have hL := (congrArg (fun t : LowerPair × Bool × Bool =>
    (trunkEndpointCases C t.1 t.2.1 t.2.2).map Prod.fst) hl).trans hLeft
  have hR := (congrArg (fun t : LowerPair × Bool × Bool =>
    (trunkEndpointCases C t.1 t.2.1 t.2.2).map Prod.fst) hr).trans hRight
  unfold automaticFlags
  rw [hL, hR]

private abbrev specAt7 (pi goal : ℕ) : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 7) pi))[goal-1]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private abbrev cSpec7_0_1 := specAt7 0 1
private theorem cFlags7_0_1 : automaticFlags (trunkCatalog.states 7).context cSpec7_0_1 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_2 coordinateInput7_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_2 hCoordinate7_1]
  decide +kernel
private abbrev cSpec7_0_2 := specAt7 0 2
private theorem cFlags7_0_2 : automaticFlags (trunkCatalog.states 7).context cSpec7_0_2 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_4 coordinateInput7_5 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_4 hCoordinate7_5]
  decide +kernel
private abbrev cSpec7_0_3 := specAt7 0 3
private theorem cFlags7_0_3 : automaticFlags (trunkCatalog.states 7).context cSpec7_0_3 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_6 coordinateInput7_7 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_6 hCoordinate7_7]
  decide +kernel
private abbrev cSpec7_0_4 := specAt7 0 4
private theorem cFlags7_0_4 : automaticFlags (trunkCatalog.states 7).context cSpec7_0_4 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_8 coordinateInput7_9 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_8 hCoordinate7_9]
  decide +kernel
private abbrev cSpec7_0_5 := specAt7 0 5
private theorem cFlags7_0_5 : automaticFlags (trunkCatalog.states 7).context cSpec7_0_5 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_10 coordinateInput7_11 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_10 hCoordinate7_11]
  decide +kernel
private abbrev cSpec7_0_6 := specAt7 0 6
private theorem cFlags7_0_6 : automaticFlags (trunkCatalog.states 7).context cSpec7_0_6 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_0 coordinateInput7_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_0 hCoordinate7_3]
  decide +kernel
private abbrev cSpec7_0_7 := specAt7 0 7
private theorem cFlags7_0_7 : automaticFlags (trunkCatalog.states 7).context cSpec7_0_7 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_12 coordinateInput7_13 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_12 hCoordinate7_13]
  decide +kernel
private abbrev cSpec7_0_8 := specAt7 0 8
private theorem cFlags7_0_8 : automaticFlags (trunkCatalog.states 7).context cSpec7_0_8 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_14 coordinateInput7_15 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_14 hCoordinate7_15]
  decide +kernel
private abbrev cSpec7_0_9 := specAt7 0 9
private theorem cFlags7_0_9 : automaticFlags (trunkCatalog.states 7).context cSpec7_0_9 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_16 coordinateInput7_17 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_16 hCoordinate7_17]
  decide +kernel
private abbrev cSpec7_0_10 := specAt7 0 10
private theorem cFlags7_0_10 : automaticFlags (trunkCatalog.states 7).context cSpec7_0_10 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_18 coordinateInput7_19 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_18 hCoordinate7_19]
  decide +kernel
private abbrev cSpec7_0_11 := specAt7 0 11
private theorem cFlags7_0_11 : automaticFlags (trunkCatalog.states 7).context cSpec7_0_11 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_20 coordinateInput7_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_20 hCoordinate7_21]
  decide +kernel
private abbrev cSpec7_0_12 := specAt7 0 12
private theorem cFlags7_0_12 : automaticFlags (trunkCatalog.states 7).context cSpec7_0_12 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_22 coordinateInput7_23 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_22 hCoordinate7_23]
  decide +kernel
private abbrev cSpec7_0_13 := specAt7 0 13
private theorem cFlags7_0_13 : automaticFlags (trunkCatalog.states 7).context cSpec7_0_13 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_24 coordinateInput7_25 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_24 hCoordinate7_25]
  decide +kernel
private abbrev cSpec7_0_14 := specAt7 0 14
private theorem cFlags7_0_14 : automaticFlags (trunkCatalog.states 7).context cSpec7_0_14 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_26 coordinateInput7_27 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_26 hCoordinate7_27]
  decide +kernel
private abbrev cSpec7_0_15 := specAt7 0 15
private theorem cFlags7_0_15 : automaticFlags (trunkCatalog.states 7).context cSpec7_0_15 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_28 coordinateInput7_29 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_28 hCoordinate7_29]
  decide +kernel
private abbrev cSpec7_0_16 := specAt7 0 16
private theorem cFlags7_0_16 : automaticFlags (trunkCatalog.states 7).context cSpec7_0_16 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_2 coordinateInput7_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_2 hCoordinate7_3]
  decide +kernel
private abbrev cSpec7_0_17 := specAt7 0 17
private theorem cFlags7_0_17 : automaticFlags (trunkCatalog.states 7).context cSpec7_0_17 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_0 coordinateInput7_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_0 hCoordinate7_1]
  decide +kernel
private abbrev cSpec7_0_18 := specAt7 0 18
private theorem cFlags7_0_18 : automaticFlags (trunkCatalog.states 7).context cSpec7_0_18 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_0 coordinateInput7_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_0 hCoordinate7_21]
  decide +kernel
private abbrev cSpec7_0_19 := specAt7 0 19
private theorem cFlags7_0_19 : automaticFlags (trunkCatalog.states 7).context cSpec7_0_19 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_20 coordinateInput7_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_20 hCoordinate7_3]
  decide +kernel
private abbrev cSpec7_0_20 := specAt7 0 20
private theorem cFlags7_0_20 : automaticFlags (trunkCatalog.states 7).context cSpec7_0_20 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  rw [automaticFlags_cached _ _ coordinateInput7_2 coordinateInput7_30 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_2 hCoordinate7_30]
  decide +kernel
private abbrev cSpec7_0_21 := specAt7 0 21
private theorem cFlags7_0_21 : automaticFlags (trunkCatalog.states 7).context cSpec7_0_21 = (List.replicate 2 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_31 coordinateInput7_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_31 hCoordinate7_21]
  decide +kernel
private abbrev cSpec7_1_1 := specAt7 1 1
private theorem cFlags7_1_1 : automaticFlags (trunkCatalog.states 7).context cSpec7_1_1 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_2 coordinateInput7_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_2 hCoordinate7_1]
  decide +kernel
private abbrev cSpec7_1_2 := specAt7 1 2
private theorem cFlags7_1_2 : automaticFlags (trunkCatalog.states 7).context cSpec7_1_2 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_4 coordinateInput7_5 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_4 hCoordinate7_5]
  decide +kernel
private abbrev cSpec7_1_3 := specAt7 1 3
private theorem cFlags7_1_3 : automaticFlags (trunkCatalog.states 7).context cSpec7_1_3 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_6 coordinateInput7_7 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_6 hCoordinate7_7]
  decide +kernel
private abbrev cSpec7_1_4 := specAt7 1 4
private theorem cFlags7_1_4 : automaticFlags (trunkCatalog.states 7).context cSpec7_1_4 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_8 coordinateInput7_9 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_8 hCoordinate7_9]
  decide +kernel
private abbrev cSpec7_1_5 := specAt7 1 5
private theorem cFlags7_1_5 : automaticFlags (trunkCatalog.states 7).context cSpec7_1_5 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_10 coordinateInput7_11 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_10 hCoordinate7_11]
  decide +kernel
private abbrev cSpec7_1_6 := specAt7 1 6
private theorem cFlags7_1_6 : automaticFlags (trunkCatalog.states 7).context cSpec7_1_6 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_0 coordinateInput7_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_0 hCoordinate7_3]
  decide +kernel
private abbrev cSpec7_1_7 := specAt7 1 7
private theorem cFlags7_1_7 : automaticFlags (trunkCatalog.states 7).context cSpec7_1_7 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_12 coordinateInput7_13 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_12 hCoordinate7_13]
  decide +kernel
private abbrev cSpec7_1_8 := specAt7 1 8
private theorem cFlags7_1_8 : automaticFlags (trunkCatalog.states 7).context cSpec7_1_8 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_14 coordinateInput7_15 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_14 hCoordinate7_15]
  decide +kernel
private abbrev cSpec7_1_9 := specAt7 1 9
private theorem cFlags7_1_9 : automaticFlags (trunkCatalog.states 7).context cSpec7_1_9 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_16 coordinateInput7_17 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_16 hCoordinate7_17]
  decide +kernel
private abbrev cSpec7_1_10 := specAt7 1 10
private theorem cFlags7_1_10 : automaticFlags (trunkCatalog.states 7).context cSpec7_1_10 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_18 coordinateInput7_19 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_18 hCoordinate7_19]
  decide +kernel
private abbrev cSpec7_1_11 := specAt7 1 11
private theorem cFlags7_1_11 : automaticFlags (trunkCatalog.states 7).context cSpec7_1_11 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_32 coordinateInput7_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_32 hCoordinate7_33]
  decide +kernel
private abbrev cSpec7_1_12 := specAt7 1 12
private theorem cFlags7_1_12 : automaticFlags (trunkCatalog.states 7).context cSpec7_1_12 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_34 coordinateInput7_35 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_34 hCoordinate7_35]
  decide +kernel
private abbrev cSpec7_1_13 := specAt7 1 13
private theorem cFlags7_1_13 : automaticFlags (trunkCatalog.states 7).context cSpec7_1_13 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_36 coordinateInput7_37 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_36 hCoordinate7_37]
  decide +kernel
private abbrev cSpec7_1_14 := specAt7 1 14
private theorem cFlags7_1_14 : automaticFlags (trunkCatalog.states 7).context cSpec7_1_14 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_38 coordinateInput7_39 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_38 hCoordinate7_39]
  decide +kernel
private abbrev cSpec7_1_15 := specAt7 1 15
private theorem cFlags7_1_15 : automaticFlags (trunkCatalog.states 7).context cSpec7_1_15 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_40 coordinateInput7_41 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_40 hCoordinate7_41]
  decide +kernel
private abbrev cSpec7_1_16 := specAt7 1 16
private theorem cFlags7_1_16 : automaticFlags (trunkCatalog.states 7).context cSpec7_1_16 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_2 coordinateInput7_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_2 hCoordinate7_3]
  decide +kernel
private abbrev cSpec7_1_17 := specAt7 1 17
private theorem cFlags7_1_17 : automaticFlags (trunkCatalog.states 7).context cSpec7_1_17 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_0 coordinateInput7_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_0 hCoordinate7_1]
  decide +kernel
private abbrev cSpec7_1_18 := specAt7 1 18
private theorem cFlags7_1_18 : automaticFlags (trunkCatalog.states 7).context cSpec7_1_18 = (List.replicate 5 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_0 coordinateInput7_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_0 hCoordinate7_33]
  decide +kernel
private abbrev cSpec7_1_19 := specAt7 1 19
private theorem cFlags7_1_19 : automaticFlags (trunkCatalog.states 7).context cSpec7_1_19 = (List.replicate 8 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_32 coordinateInput7_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_32 hCoordinate7_3]
  decide +kernel
private abbrev cSpec7_1_20 := specAt7 1 20
private theorem cFlags7_1_20 : automaticFlags (trunkCatalog.states 7).context cSpec7_1_20 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  rw [automaticFlags_cached _ _ coordinateInput7_2 coordinateInput7_30 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_2 hCoordinate7_30]
  decide +kernel
private abbrev cSpec7_1_21 := specAt7 1 21
private theorem cFlags7_1_21 : automaticFlags (trunkCatalog.states 7).context cSpec7_1_21 = (List.replicate 1 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_31 coordinateInput7_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_31 hCoordinate7_33]
  decide +kernel
private abbrev cSpec7_2_1 := specAt7 2 1
private theorem cFlags7_2_1 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_1 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_2 coordinateInput7_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_2 hCoordinate7_1]
  decide +kernel
private abbrev cSpec7_2_2 := specAt7 2 2
private theorem cFlags7_2_2 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_2 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_4 coordinateInput7_5 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_4 hCoordinate7_5]
  decide +kernel
private abbrev cSpec7_2_3 := specAt7 2 3
private theorem cFlags7_2_3 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_3 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_6 coordinateInput7_7 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_6 hCoordinate7_7]
  decide +kernel
private abbrev cSpec7_2_4 := specAt7 2 4
private theorem cFlags7_2_4 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_4 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_8 coordinateInput7_9 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_8 hCoordinate7_9]
  decide +kernel
private abbrev cSpec7_2_5 := specAt7 2 5
private theorem cFlags7_2_5 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_5 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_10 coordinateInput7_11 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_10 hCoordinate7_11]
  decide +kernel
private abbrev cSpec7_2_6 := specAt7 2 6
private theorem cFlags7_2_6 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_6 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_0 coordinateInput7_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_0 hCoordinate7_3]
  decide +kernel
private abbrev cSpec7_2_7 := specAt7 2 7
private theorem cFlags7_2_7 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_7 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_12 coordinateInput7_13 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_12 hCoordinate7_13]
  decide +kernel
private abbrev cSpec7_2_8 := specAt7 2 8
private theorem cFlags7_2_8 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_8 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_14 coordinateInput7_15 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_14 hCoordinate7_15]
  decide +kernel
private abbrev cSpec7_2_9 := specAt7 2 9
private theorem cFlags7_2_9 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_9 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_16 coordinateInput7_17 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_16 hCoordinate7_17]
  decide +kernel
private abbrev cSpec7_2_10 := specAt7 2 10
private theorem cFlags7_2_10 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_10 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_18 coordinateInput7_19 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_18 hCoordinate7_19]
  decide +kernel
private abbrev cSpec7_2_11 := specAt7 2 11
private theorem cFlags7_2_11 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_11 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_42 coordinateInput7_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_42 hCoordinate7_43]
  decide +kernel
private abbrev cSpec7_2_12 := specAt7 2 12
private theorem cFlags7_2_12 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_12 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_44 coordinateInput7_45 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_44 hCoordinate7_45]
  decide +kernel
private abbrev cSpec7_2_13 := specAt7 2 13
private theorem cFlags7_2_13 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_13 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_46 coordinateInput7_47 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_46 hCoordinate7_47]
  decide +kernel
private abbrev cSpec7_2_14 := specAt7 2 14
private theorem cFlags7_2_14 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_14 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_48 coordinateInput7_49 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_48 hCoordinate7_49]
  decide +kernel
private abbrev cSpec7_2_15 := specAt7 2 15
private theorem cFlags7_2_15 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_15 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_50 coordinateInput7_51 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_50 hCoordinate7_51]
  decide +kernel
private abbrev cSpec7_2_16 := specAt7 2 16
private theorem cFlags7_2_16 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_16 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_32 coordinateInput7_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_32 hCoordinate7_33]
  decide +kernel
private abbrev cSpec7_2_17 := specAt7 2 17
private theorem cFlags7_2_17 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_17 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_34 coordinateInput7_35 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_34 hCoordinate7_35]
  decide +kernel
private abbrev cSpec7_2_18 := specAt7 2 18
private theorem cFlags7_2_18 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_18 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_36 coordinateInput7_37 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_36 hCoordinate7_37]
  decide +kernel
private abbrev cSpec7_2_19 := specAt7 2 19
private theorem cFlags7_2_19 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_19 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_38 coordinateInput7_39 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_38 hCoordinate7_39]
  decide +kernel
private abbrev cSpec7_2_20 := specAt7 2 20
private theorem cFlags7_2_20 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_20 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_40 coordinateInput7_41 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_40 hCoordinate7_41]
  decide +kernel
private abbrev cSpec7_2_21 := specAt7 2 21
private theorem cFlags7_2_21 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_21 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_2 coordinateInput7_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_2 hCoordinate7_3]
  decide +kernel
private abbrev cSpec7_2_22 := specAt7 2 22
private theorem cFlags7_2_22 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_22 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_0 coordinateInput7_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_0 hCoordinate7_1]
  decide +kernel
private abbrev cSpec7_2_23 := specAt7 2 23
private theorem cFlags7_2_23 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_23 = (List.replicate 20 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_0 coordinateInput7_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_0 hCoordinate7_43]
  decide +kernel
private abbrev cSpec7_2_24 := specAt7 2 24
private theorem cFlags7_2_24 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_24 = (List.replicate 8 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_42 coordinateInput7_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_42 hCoordinate7_3]
  decide +kernel
private abbrev cSpec7_2_25 := specAt7 2 25
private theorem cFlags7_2_25 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_25 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  rw [automaticFlags_cached _ _ coordinateInput7_2 coordinateInput7_30 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_2 hCoordinate7_30]
  decide +kernel
private abbrev cSpec7_2_26 := specAt7 2 26
private theorem cFlags7_2_26 : automaticFlags (trunkCatalog.states 7).context cSpec7_2_26 = (List.replicate 1 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_31 coordinateInput7_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_31 hCoordinate7_33]
  decide +kernel
private abbrev cSpec7_3_1 := specAt7 3 1
private theorem cFlags7_3_1 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_1 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_2 coordinateInput7_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_2 hCoordinate7_1]
  decide +kernel
private abbrev cSpec7_3_2 := specAt7 3 2
private theorem cFlags7_3_2 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_2 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_4 coordinateInput7_5 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_4 hCoordinate7_5]
  decide +kernel
private abbrev cSpec7_3_3 := specAt7 3 3
private theorem cFlags7_3_3 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_3 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_6 coordinateInput7_7 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_6 hCoordinate7_7]
  decide +kernel
private abbrev cSpec7_3_4 := specAt7 3 4
private theorem cFlags7_3_4 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_4 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_8 coordinateInput7_9 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_8 hCoordinate7_9]
  decide +kernel
private abbrev cSpec7_3_5 := specAt7 3 5
private theorem cFlags7_3_5 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_5 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_10 coordinateInput7_11 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_10 hCoordinate7_11]
  decide +kernel
private abbrev cSpec7_3_6 := specAt7 3 6
private theorem cFlags7_3_6 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_6 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_52 coordinateInput7_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_52 hCoordinate7_53]
  decide +kernel
private abbrev cSpec7_3_7 := specAt7 3 7
private theorem cFlags7_3_7 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_7 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_54 coordinateInput7_55 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_54 hCoordinate7_55]
  decide +kernel
private abbrev cSpec7_3_8 := specAt7 3 8
private theorem cFlags7_3_8 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_8 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_56 coordinateInput7_57 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_56 hCoordinate7_57]
  decide +kernel
private abbrev cSpec7_3_9 := specAt7 3 9
private theorem cFlags7_3_9 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_9 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_58 coordinateInput7_59 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_58 hCoordinate7_59]
  decide +kernel
private abbrev cSpec7_3_10 := specAt7 3 10
private theorem cFlags7_3_10 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_10 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_60 coordinateInput7_61 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_60 hCoordinate7_61]
  decide +kernel
private abbrev cSpec7_3_11 := specAt7 3 11
private theorem cFlags7_3_11 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_11 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_62 coordinateInput7_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_62 hCoordinate7_63]
  decide +kernel
private abbrev cSpec7_3_12 := specAt7 3 12
private theorem cFlags7_3_12 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_12 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_64 coordinateInput7_65 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_64 hCoordinate7_65]
  decide +kernel
private abbrev cSpec7_3_13 := specAt7 3 13
private theorem cFlags7_3_13 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_13 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_66 coordinateInput7_67 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_66 hCoordinate7_67]
  decide +kernel
private abbrev cSpec7_3_14 := specAt7 3 14
private theorem cFlags7_3_14 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_14 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_68 coordinateInput7_69 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_68 hCoordinate7_69]
  decide +kernel
private abbrev cSpec7_3_15 := specAt7 3 15
private theorem cFlags7_3_15 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_15 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_70 coordinateInput7_71 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_70 hCoordinate7_71]
  decide +kernel
private abbrev cSpec7_3_16 := specAt7 3 16
private theorem cFlags7_3_16 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_16 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_42 coordinateInput7_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_42 hCoordinate7_43]
  decide +kernel
private abbrev cSpec7_3_17 := specAt7 3 17
private theorem cFlags7_3_17 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_17 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_44 coordinateInput7_45 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_44 hCoordinate7_45]
  decide +kernel
private abbrev cSpec7_3_18 := specAt7 3 18
private theorem cFlags7_3_18 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_18 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_46 coordinateInput7_47 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_46 hCoordinate7_47]
  decide +kernel
private abbrev cSpec7_3_19 := specAt7 3 19
private theorem cFlags7_3_19 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_19 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_48 coordinateInput7_49 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_48 hCoordinate7_49]
  decide +kernel
private abbrev cSpec7_3_20 := specAt7 3 20
private theorem cFlags7_3_20 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_20 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_50 coordinateInput7_51 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_50 hCoordinate7_51]
  decide +kernel
private abbrev cSpec7_3_21 := specAt7 3 21
private theorem cFlags7_3_21 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_21 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_72 coordinateInput7_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_72 hCoordinate7_73]
  decide +kernel
private abbrev cSpec7_3_22 := specAt7 3 22
private theorem cFlags7_3_22 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_22 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_74 coordinateInput7_75 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_74 hCoordinate7_75]
  decide +kernel
private abbrev cSpec7_3_23 := specAt7 3 23
private theorem cFlags7_3_23 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_23 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_76 coordinateInput7_77 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_76 hCoordinate7_77]
  decide +kernel
private abbrev cSpec7_3_24 := specAt7 3 24
private theorem cFlags7_3_24 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_24 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_78 coordinateInput7_79 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_78 hCoordinate7_79]
  decide +kernel
private abbrev cSpec7_3_25 := specAt7 3 25
private theorem cFlags7_3_25 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_25 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_80 coordinateInput7_81 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_80 hCoordinate7_81]
  decide +kernel
private abbrev cSpec7_3_26 := specAt7 3 26
private theorem cFlags7_3_26 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_26 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_32 coordinateInput7_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_32 hCoordinate7_33]
  decide +kernel
private abbrev cSpec7_3_27 := specAt7 3 27
private theorem cFlags7_3_27 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_27 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_34 coordinateInput7_35 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_34 hCoordinate7_35]
  decide +kernel
private abbrev cSpec7_3_28 := specAt7 3 28
private theorem cFlags7_3_28 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_28 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_36 coordinateInput7_37 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_36 hCoordinate7_37]
  decide +kernel
private abbrev cSpec7_3_29 := specAt7 3 29
private theorem cFlags7_3_29 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_29 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_38 coordinateInput7_39 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_38 hCoordinate7_39]
  decide +kernel
private abbrev cSpec7_3_30 := specAt7 3 30
private theorem cFlags7_3_30 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_30 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_40 coordinateInput7_41 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_40 hCoordinate7_41]
  decide +kernel
private abbrev cSpec7_3_31 := specAt7 3 31
private theorem cFlags7_3_31 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_31 = (List.replicate 20 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_2 coordinateInput7_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_2 hCoordinate7_53]
  decide +kernel
private abbrev cSpec7_3_32 := specAt7 3 32
private theorem cFlags7_3_32 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_32 = (List.replicate 8 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_52 coordinateInput7_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_52 hCoordinate7_1]
  decide +kernel
private abbrev cSpec7_3_33 := specAt7 3 33
private theorem cFlags7_3_33 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_33 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_52 coordinateInput7_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_52 hCoordinate7_63]
  decide +kernel
private abbrev cSpec7_3_34 := specAt7 3 34
private theorem cFlags7_3_34 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_34 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_62 coordinateInput7_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_62 hCoordinate7_53]
  decide +kernel
private abbrev cSpec7_3_35 := specAt7 3 35
private theorem cFlags7_3_35 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_35 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_62 coordinateInput7_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_62 hCoordinate7_43]
  decide +kernel
private abbrev cSpec7_3_36 := specAt7 3 36
private theorem cFlags7_3_36 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_36 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_42 coordinateInput7_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_42 hCoordinate7_63]
  decide +kernel
private abbrev cSpec7_3_37 := specAt7 3 37
private theorem cFlags7_3_37 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_37 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_42 coordinateInput7_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_42 hCoordinate7_73]
  decide +kernel
private abbrev cSpec7_3_38 := specAt7 3 38
private theorem cFlags7_3_38 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_38 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_72 coordinateInput7_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_72 hCoordinate7_43]
  decide +kernel
private abbrev cSpec7_3_39 := specAt7 3 39
private theorem cFlags7_3_39 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_39 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_72 coordinateInput7_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_72 hCoordinate7_33]
  decide +kernel
private abbrev cSpec7_3_40 := specAt7 3 40
private theorem cFlags7_3_40 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_40 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_32 coordinateInput7_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_32 hCoordinate7_73]
  decide +kernel
private abbrev cSpec7_3_41 := specAt7 3 41
private theorem cFlags7_3_41 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_41 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  rw [automaticFlags_cached _ _ coordinateInput7_2 coordinateInput7_30 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_2 hCoordinate7_30]
  decide +kernel
private abbrev cSpec7_3_42 := specAt7 3 42
private theorem cFlags7_3_42 : automaticFlags (trunkCatalog.states 7).context cSpec7_3_42 = (List.replicate 1 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_31 coordinateInput7_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_31 hCoordinate7_33]
  decide +kernel
private abbrev cSpec7_4_1 := specAt7 4 1
private theorem cFlags7_4_1 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_1 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_2 coordinateInput7_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_2 hCoordinate7_1]
  decide +kernel
private abbrev cSpec7_4_2 := specAt7 4 2
private theorem cFlags7_4_2 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_2 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_4 coordinateInput7_5 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_4 hCoordinate7_5]
  decide +kernel
private abbrev cSpec7_4_3 := specAt7 4 3
private theorem cFlags7_4_3 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_3 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_6 coordinateInput7_7 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_6 hCoordinate7_7]
  decide +kernel
private abbrev cSpec7_4_4 := specAt7 4 4
private theorem cFlags7_4_4 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_4 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_8 coordinateInput7_9 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_8 hCoordinate7_9]
  decide +kernel
private abbrev cSpec7_4_5 := specAt7 4 5
private theorem cFlags7_4_5 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_5 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_10 coordinateInput7_11 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_10 hCoordinate7_11]
  decide +kernel
private abbrev cSpec7_4_6 := specAt7 4 6
private theorem cFlags7_4_6 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_6 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_52 coordinateInput7_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_52 hCoordinate7_53]
  decide +kernel
private abbrev cSpec7_4_7 := specAt7 4 7
private theorem cFlags7_4_7 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_7 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_54 coordinateInput7_55 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_54 hCoordinate7_55]
  decide +kernel
private abbrev cSpec7_4_8 := specAt7 4 8
private theorem cFlags7_4_8 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_8 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_56 coordinateInput7_57 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_56 hCoordinate7_57]
  decide +kernel
private abbrev cSpec7_4_9 := specAt7 4 9
private theorem cFlags7_4_9 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_9 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_58 coordinateInput7_59 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_58 hCoordinate7_59]
  decide +kernel
private abbrev cSpec7_4_10 := specAt7 4 10
private theorem cFlags7_4_10 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_10 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_60 coordinateInput7_61 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_60 hCoordinate7_61]
  decide +kernel
private abbrev cSpec7_4_11 := specAt7 4 11
private theorem cFlags7_4_11 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_11 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_82 coordinateInput7_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_82 hCoordinate7_83]
  decide +kernel
private abbrev cSpec7_4_12 := specAt7 4 12
private theorem cFlags7_4_12 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_12 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_84 coordinateInput7_85 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_84 hCoordinate7_85]
  decide +kernel
private abbrev cSpec7_4_13 := specAt7 4 13
private theorem cFlags7_4_13 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_13 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_86 coordinateInput7_87 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_86 hCoordinate7_87]
  decide +kernel
private abbrev cSpec7_4_14 := specAt7 4 14
private theorem cFlags7_4_14 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_14 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_88 coordinateInput7_89 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_88 hCoordinate7_89]
  decide +kernel
private abbrev cSpec7_4_15 := specAt7 4 15
private theorem cFlags7_4_15 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_15 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_90 coordinateInput7_91 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_90 hCoordinate7_91]
  decide +kernel
private abbrev cSpec7_4_16 := specAt7 4 16
private theorem cFlags7_4_16 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_16 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_42 coordinateInput7_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_42 hCoordinate7_43]
  decide +kernel
private abbrev cSpec7_4_17 := specAt7 4 17
private theorem cFlags7_4_17 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_17 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_44 coordinateInput7_45 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_44 hCoordinate7_45]
  decide +kernel
private abbrev cSpec7_4_18 := specAt7 4 18
private theorem cFlags7_4_18 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_18 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_46 coordinateInput7_47 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_46 hCoordinate7_47]
  decide +kernel
private abbrev cSpec7_4_19 := specAt7 4 19
private theorem cFlags7_4_19 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_19 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_48 coordinateInput7_49 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_48 hCoordinate7_49]
  decide +kernel
private abbrev cSpec7_4_20 := specAt7 4 20
private theorem cFlags7_4_20 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_20 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_50 coordinateInput7_51 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_50 hCoordinate7_51]
  decide +kernel
private abbrev cSpec7_4_21 := specAt7 4 21
private theorem cFlags7_4_21 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_21 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_72 coordinateInput7_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_72 hCoordinate7_73]
  decide +kernel
private abbrev cSpec7_4_22 := specAt7 4 22
private theorem cFlags7_4_22 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_22 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_74 coordinateInput7_75 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_74 hCoordinate7_75]
  decide +kernel
private abbrev cSpec7_4_23 := specAt7 4 23
private theorem cFlags7_4_23 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_23 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_76 coordinateInput7_77 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_76 hCoordinate7_77]
  decide +kernel
private abbrev cSpec7_4_24 := specAt7 4 24
private theorem cFlags7_4_24 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_24 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_78 coordinateInput7_79 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_78 hCoordinate7_79]
  decide +kernel
private abbrev cSpec7_4_25 := specAt7 4 25
private theorem cFlags7_4_25 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_25 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_80 coordinateInput7_81 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_80 hCoordinate7_81]
  decide +kernel
private abbrev cSpec7_4_26 := specAt7 4 26
private theorem cFlags7_4_26 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_26 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_32 coordinateInput7_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_32 hCoordinate7_33]
  decide +kernel
private abbrev cSpec7_4_27 := specAt7 4 27
private theorem cFlags7_4_27 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_27 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_34 coordinateInput7_35 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_34 hCoordinate7_35]
  decide +kernel
private abbrev cSpec7_4_28 := specAt7 4 28
private theorem cFlags7_4_28 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_28 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_36 coordinateInput7_37 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_36 hCoordinate7_37]
  decide +kernel
private abbrev cSpec7_4_29 := specAt7 4 29
private theorem cFlags7_4_29 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_29 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_38 coordinateInput7_39 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_38 hCoordinate7_39]
  decide +kernel
private abbrev cSpec7_4_30 := specAt7 4 30
private theorem cFlags7_4_30 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_30 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_40 coordinateInput7_41 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_40 hCoordinate7_41]
  decide +kernel
private abbrev cSpec7_4_31 := specAt7 4 31
private theorem cFlags7_4_31 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_31 = (List.replicate 20 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_2 coordinateInput7_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_2 hCoordinate7_53]
  decide +kernel
private abbrev cSpec7_4_32 := specAt7 4 32
private theorem cFlags7_4_32 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_32 = (List.replicate 8 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_52 coordinateInput7_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_52 hCoordinate7_1]
  decide +kernel
private abbrev cSpec7_4_33 := specAt7 4 33
private theorem cFlags7_4_33 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_33 = (List.replicate 8 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_52 coordinateInput7_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_52 hCoordinate7_83]
  decide +kernel
private abbrev cSpec7_4_34 := specAt7 4 34
private theorem cFlags7_4_34 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_34 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_82 coordinateInput7_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_82 hCoordinate7_53]
  decide +kernel
private abbrev cSpec7_4_35 := specAt7 4 35
private theorem cFlags7_4_35 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_35 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_82 coordinateInput7_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_82 hCoordinate7_43]
  decide +kernel
private abbrev cSpec7_4_36 := specAt7 4 36
private theorem cFlags7_4_36 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_36 = (List.replicate 8 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_42 coordinateInput7_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_42 hCoordinate7_83]
  decide +kernel
private abbrev cSpec7_4_37 := specAt7 4 37
private theorem cFlags7_4_37 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_37 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_42 coordinateInput7_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_42 hCoordinate7_73]
  decide +kernel
private abbrev cSpec7_4_38 := specAt7 4 38
private theorem cFlags7_4_38 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_38 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_72 coordinateInput7_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_72 hCoordinate7_43]
  decide +kernel
private abbrev cSpec7_4_39 := specAt7 4 39
private theorem cFlags7_4_39 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_39 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_72 coordinateInput7_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_72 hCoordinate7_33]
  decide +kernel
private abbrev cSpec7_4_40 := specAt7 4 40
private theorem cFlags7_4_40 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_40 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput7_32 coordinateInput7_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_32 hCoordinate7_73]
  decide +kernel
private abbrev cSpec7_4_41 := specAt7 4 41
private theorem cFlags7_4_41 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_41 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  rw [automaticFlags_cached _ _ coordinateInput7_2 coordinateInput7_30 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_2 hCoordinate7_30]
  decide +kernel
private abbrev cSpec7_4_42 := specAt7 4 42
private theorem cFlags7_4_42 : automaticFlags (trunkCatalog.states 7).context cSpec7_4_42 = (List.replicate 1 true) := by
  rw [automaticFlags_cached _ _ coordinateInput7_31 coordinateInput7_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate7_31 hCoordinate7_33]
  decide +kernel
private theorem keys_eq : coverageKeys (trunkCatalog.states 7) = checkedKeys := by
  rfl
private theorem tasks_eq : coverageTasks (trunkCatalog.states 7) = checkedTasks := by
  rw [← coverageTasksProjection_eq]
  change [(0,[(1, (automaticFlags (trunkCatalog.states 7).context cSpec7_0_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 7).context cSpec7_0_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 7).context cSpec7_0_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 7).context cSpec7_0_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 7).context cSpec7_0_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 7).context cSpec7_0_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 7).context cSpec7_0_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 7).context cSpec7_0_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 7).context cSpec7_0_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 7).context cSpec7_0_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 7).context cSpec7_0_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 7).context cSpec7_0_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 7).context cSpec7_0_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 7).context cSpec7_0_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 7).context cSpec7_0_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 7).context cSpec7_0_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 7).context cSpec7_0_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 7).context cSpec7_0_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 7).context cSpec7_0_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 7).context cSpec7_0_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 7).context cSpec7_0_21).zipIdx.map Prod.swap)]),(1,[(1, (automaticFlags (trunkCatalog.states 7).context cSpec7_1_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 7).context cSpec7_1_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 7).context cSpec7_1_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 7).context cSpec7_1_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 7).context cSpec7_1_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 7).context cSpec7_1_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 7).context cSpec7_1_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 7).context cSpec7_1_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 7).context cSpec7_1_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 7).context cSpec7_1_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 7).context cSpec7_1_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 7).context cSpec7_1_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 7).context cSpec7_1_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 7).context cSpec7_1_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 7).context cSpec7_1_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 7).context cSpec7_1_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 7).context cSpec7_1_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 7).context cSpec7_1_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 7).context cSpec7_1_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 7).context cSpec7_1_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 7).context cSpec7_1_21).zipIdx.map Prod.swap)]),(2,[(1, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 7).context cSpec7_2_26).zipIdx.map Prod.swap)]),(3,[(1, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 7).context cSpec7_3_42).zipIdx.map Prod.swap)]),(4,[(1, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 7).context cSpec7_4_42).zipIdx.map Prod.swap)])] = checkedTasks
  rw [cFlags7_0_1, cFlags7_0_2, cFlags7_0_3, cFlags7_0_4, cFlags7_0_5, cFlags7_0_6, cFlags7_0_7, cFlags7_0_8, cFlags7_0_9, cFlags7_0_10, cFlags7_0_11, cFlags7_0_12, cFlags7_0_13, cFlags7_0_14, cFlags7_0_15, cFlags7_0_16, cFlags7_0_17, cFlags7_0_18, cFlags7_0_19, cFlags7_0_20, cFlags7_0_21, cFlags7_1_1, cFlags7_1_2, cFlags7_1_3, cFlags7_1_4, cFlags7_1_5, cFlags7_1_6, cFlags7_1_7, cFlags7_1_8, cFlags7_1_9, cFlags7_1_10, cFlags7_1_11, cFlags7_1_12, cFlags7_1_13, cFlags7_1_14, cFlags7_1_15, cFlags7_1_16, cFlags7_1_17, cFlags7_1_18, cFlags7_1_19, cFlags7_1_20, cFlags7_1_21, cFlags7_2_1, cFlags7_2_2, cFlags7_2_3, cFlags7_2_4, cFlags7_2_5, cFlags7_2_6, cFlags7_2_7, cFlags7_2_8, cFlags7_2_9, cFlags7_2_10, cFlags7_2_11, cFlags7_2_12, cFlags7_2_13, cFlags7_2_14, cFlags7_2_15, cFlags7_2_16, cFlags7_2_17, cFlags7_2_18, cFlags7_2_19, cFlags7_2_20, cFlags7_2_21, cFlags7_2_22, cFlags7_2_23, cFlags7_2_24, cFlags7_2_25, cFlags7_2_26, cFlags7_3_1, cFlags7_3_2, cFlags7_3_3, cFlags7_3_4, cFlags7_3_5, cFlags7_3_6, cFlags7_3_7, cFlags7_3_8, cFlags7_3_9, cFlags7_3_10, cFlags7_3_11, cFlags7_3_12, cFlags7_3_13, cFlags7_3_14, cFlags7_3_15, cFlags7_3_16, cFlags7_3_17, cFlags7_3_18, cFlags7_3_19, cFlags7_3_20, cFlags7_3_21, cFlags7_3_22, cFlags7_3_23, cFlags7_3_24, cFlags7_3_25, cFlags7_3_26, cFlags7_3_27, cFlags7_3_28, cFlags7_3_29, cFlags7_3_30, cFlags7_3_31, cFlags7_3_32, cFlags7_3_33, cFlags7_3_34, cFlags7_3_35, cFlags7_3_36, cFlags7_3_37, cFlags7_3_38, cFlags7_3_39, cFlags7_3_40, cFlags7_3_41, cFlags7_3_42, cFlags7_4_1, cFlags7_4_2, cFlags7_4_3, cFlags7_4_4, cFlags7_4_5, cFlags7_4_6, cFlags7_4_7, cFlags7_4_8, cFlags7_4_9, cFlags7_4_10, cFlags7_4_11, cFlags7_4_12, cFlags7_4_13, cFlags7_4_14, cFlags7_4_15, cFlags7_4_16, cFlags7_4_17, cFlags7_4_18, cFlags7_4_19, cFlags7_4_20, cFlags7_4_21, cFlags7_4_22, cFlags7_4_23, cFlags7_4_24, cFlags7_4_25, cFlags7_4_26, cFlags7_4_27, cFlags7_4_28, cFlags7_4_29, cFlags7_4_30, cFlags7_4_31, cFlags7_4_32, cFlags7_4_33, cFlags7_4_34, cFlags7_4_35, cFlags7_4_36, cFlags7_4_37, cFlags7_4_38, cFlags7_4_39, cFlags7_4_40, cFlags7_4_41, cFlags7_4_42]
  rfl
private theorem parents_length : (trunkRawParents (trunkCatalog.states 7).context).length = 100 := by
  decide +kernel
private theorem table_checked : coverageTable checkedKeys checkedTasks 100 := by
  apply coverageRemainder_sound _ _ _ [[21, 41], [], [41, 53, 73, 93], [73, 75], [75]]
  unfold coverageRemainder parentsFor
  decide +kernel

theorem solution : trunkCoverage trunkCatalog 7 := by
  apply coverageTable_sound 7
  · unfold certRectangleValid; decide +kernel
  · decide +kernel
  · rw [keys_eq, tasks_eq, parents_length]
    exact table_checked
#print axioms solution
