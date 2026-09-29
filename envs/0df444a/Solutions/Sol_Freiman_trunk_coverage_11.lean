-- Prove2me | solution 1 for Freiman.trunk_coverage_11
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:52:43.480046+00:00
-- url     : https://prove2.me/submissions/9388b37d-e728-4403-ad19-6cbb6f409d14

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
      (trunkParents (trunkCatalog.states k).context).length) : trunkCoverage trunkCatalog k := by
  refine ⟨hR,h0,?_⟩
  intro pi hpi par hpar
  have hp := hpar
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

private def coordinateFields11 : Array CertField := #[⟨(4/13),(1/13),(0/1),(0/1)⟩,⟨(1/2),(1/6),(0/1),(0/1)⟩,⟨(52/73),(1/73),(0/1),(0/1)⟩,⟨(89/214),(1/214),(0/1),(0/1)⟩,⟨(9/13),(-1/13),(0/1),(0/1)⟩,⟨(15/37),(-1/37),(0/1),(0/1)⟩,⟨(22/37),(1/37),(0/1),(0/1)⟩,⟨(113/179),(1/537),(0/1),(0/1)⟩,⟨(17/22),(-1/22),(0/1),(0/1)⟩,⟨(735/1006),(1/1006),(0/1),(0/1)⟩,⟨(66/179),(-1/537),(0/1),(0/1)⟩,⟨(125/214),(-1/214),(0/1),(0/1)⟩,⟨(35/94),(1/94),(0/1),(0/1)⟩,⟨(553/1429),(1/1429),(0/1),(0/1)⟩,⟨(10/23),(-1/69),(0/1),(0/1)⟩,⟨(1272/3013),(1/3013),(0/1),(0/1)⟩,⟨(5/22),(1/22),(0/1),(0/1)⟩,⟨(42/143),(1/429),(0/1),(0/1)⟩,⟨(271/1006),(-1/1006),(0/1),(0/1)⟩,⟨(16/59),(1/177),(0/1),(0/1)⟩,⟨(767/2749),(1/2749),(0/1),(0/1)⟩,⟨(43/142),(-1/142),(0/1),(0/1)⟩,⟨(1809/6094),(1/6094),(0/1),(0/1)⟩,⟨(2/1),(-1/1),(0/1),(0/1)⟩,⟨(731/2497),(-1/2497),(0/1),(0/1)⟩,⟨(517/1249),(-1/1249),(0/1),(0/1)⟩,⟨(101/143),(-1/429),(0/1),(0/1)⟩,⟨(13/23),(1/69),(0/1),(0/1)⟩,⟨(732/1249),(1/1249),(0/1),(0/1)⟩,⟨(59/94),(-1/94),(0/1),(0/1)⟩]
private abbrev coordinateInput11_0 : LowerPair × Bool × Bool := (([2], []), true, false)
private def coordinateCodes11_0 : List (ℕ × ℕ) := [(0, 1), (0, 1), (0, 2), (0, 1), (3, 1)]
private abbrev coordinateInput11_1 : LowerPair × Bool × Bool := (([1], []), false, false)
private def coordinateCodes11_1 : List (ℕ × ℕ) := [(4, 5), (4, 5)]
private abbrev coordinateInput11_2 : LowerPair × Bool × Bool := (([1], []), true, false)
private def coordinateCodes11_2 : List (ℕ × ℕ) := [(2, 1), (2, 1)]
private abbrev coordinateInput11_3 : LowerPair × Bool × Bool := (([2], []), false, false)
private def coordinateCodes11_3 : List (ℕ × ℕ) := [(5, 5), (5, 5)]
private abbrev coordinateInput11_4 : LowerPair × Bool × Bool := (([1, 1], []), true, false)
private def coordinateCodes11_4 : List (ℕ × ℕ) := [(6, 1), (6, 2), (6, 1), (7, 1)]
private abbrev coordinateInput11_5 : LowerPair × Bool × Bool := (([1, 2], []), false, false)
private def coordinateCodes11_5 : List (ℕ × ℕ) := [(8, 5)]
private abbrev coordinateInput11_6 : LowerPair × Bool × Bool := (([1, 2], []), true, false)
private def coordinateCodes11_6 : List (ℕ × ℕ) := [(2, 1), (2, 2), (2, 1), (9, 1)]
private abbrev coordinateInput11_7 : LowerPair × Bool × Bool := (([1, 1], []), false, false)
private def coordinateCodes11_7 : List (ℕ × ℕ) := [(4, 5)]
private abbrev coordinateInput11_8 : LowerPair × Bool × Bool := (([1], [1]), true, true)
private def coordinateCodes11_8 : List (ℕ × ℕ) := [(2, 1)]
private abbrev coordinateInput11_9 : LowerPair × Bool × Bool := (([1], [2]), false, true)
private def coordinateCodes11_9 : List (ℕ × ℕ) := [(4, 5), (4, 10), (4, 5), (11, 5)]
private abbrev coordinateInput11_10 : LowerPair × Bool × Bool := (([1], [2]), true, true)
private def coordinateCodes11_10 : List (ℕ × ℕ) := [(2, 0)]
private abbrev coordinateInput11_11 : LowerPair × Bool × Bool := (([1], [1]), false, true)
private def coordinateCodes11_11 : List (ℕ × ℕ) := [(4, 4), (4, 11), (4, 4), (11, 4)]
private abbrev coordinateInput11_12 : LowerPair × Bool × Bool := (([2, 1], []), true, false)
private def coordinateCodes11_12 : List (ℕ × ℕ) := [(12, 1), (12, 2), (12, 1), (13, 1)]
private abbrev coordinateInput11_13 : LowerPair × Bool × Bool := (([2, 2], []), false, false)
private def coordinateCodes11_13 : List (ℕ × ℕ) := [(14, 5)]
private abbrev coordinateInput11_14 : LowerPair × Bool × Bool := (([2, 2], []), true, false)
private def coordinateCodes11_14 : List (ℕ × ℕ) := [(3, 1), (3, 2), (3, 1), (15, 1)]
private abbrev coordinateInput11_15 : LowerPair × Bool × Bool := (([2, 1], []), false, false)
private def coordinateCodes11_15 : List (ℕ × ℕ) := [(5, 5)]
private abbrev coordinateInput11_16 : LowerPair × Bool × Bool := (([2], [1]), true, true)
private def coordinateCodes11_16 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 1), (3, 1)]
private abbrev coordinateInput11_17 : LowerPair × Bool × Bool := (([2], [2]), false, true)
private def coordinateCodes11_17 : List (ℕ × ℕ) := [(5, 5), (5, 10), (5, 5), (10, 5)]
private abbrev coordinateInput11_18 : LowerPair × Bool × Bool := (([2], [2]), true, true)
private def coordinateCodes11_18 : List (ℕ × ℕ) := [(0, 0), (0, 3), (0, 0), (3, 0)]
private abbrev coordinateInput11_19 : LowerPair × Bool × Bool := (([2], [1]), false, true)
private def coordinateCodes11_19 : List (ℕ × ℕ) := [(5, 4), (5, 11), (5, 4), (10, 4)]
private abbrev coordinateInput11_20 : LowerPair × Bool × Bool := (([3], []), true, false)
private def coordinateCodes11_20 : List (ℕ × ℕ) := [(16, 1), (16, 1), (16, 2), (16, 1), (17, 1)]
private abbrev coordinateInput11_21 : LowerPair × Bool × Bool := (([3], []), false, false)
private def coordinateCodes11_21 : List (ℕ × ℕ) := [(18, 5), (18, 5)]
private abbrev coordinateInput11_22 : LowerPair × Bool × Bool := (([3, 1], []), true, false)
private def coordinateCodes11_22 : List (ℕ × ℕ) := [(19, 1), (19, 2), (19, 1), (20, 1)]
private abbrev coordinateInput11_23 : LowerPair × Bool × Bool := (([3, 2], []), false, false)
private def coordinateCodes11_23 : List (ℕ × ℕ) := [(21, 5)]
private abbrev coordinateInput11_24 : LowerPair × Bool × Bool := (([3, 2], []), true, false)
private def coordinateCodes11_24 : List (ℕ × ℕ) := [(17, 1), (17, 2), (17, 1), (22, 1)]
private abbrev coordinateInput11_25 : LowerPair × Bool × Bool := (([3, 1], []), false, false)
private def coordinateCodes11_25 : List (ℕ × ℕ) := [(18, 5)]
private abbrev coordinateInput11_26 : LowerPair × Bool × Bool := (([3], [1]), true, true)
private def coordinateCodes11_26 : List (ℕ × ℕ) := [(16, 1), (16, 2), (16, 1), (17, 1)]
private abbrev coordinateInput11_27 : LowerPair × Bool × Bool := (([3], [2]), false, true)
private def coordinateCodes11_27 : List (ℕ × ℕ) := [(18, 5)]
private abbrev coordinateInput11_28 : LowerPair × Bool × Bool := (([3], [2]), true, true)
private def coordinateCodes11_28 : List (ℕ × ℕ) := [(16, 0), (16, 3), (16, 0), (17, 0)]
private abbrev coordinateInput11_29 : LowerPair × Bool × Bool := (([3], [1]), false, true)
private def coordinateCodes11_29 : List (ℕ × ℕ) := [(18, 4)]
private abbrev coordinateInput11_30 : LowerPair × Bool × Bool := (([], []), true, false)
private def coordinateCodes11_30 : List (ℕ × ℕ) := [(2, 1)]
private abbrev coordinateInput11_31 : LowerPair × Bool × Bool := (([], []), false, false)
private def coordinateCodes11_31 : List (ℕ × ℕ) := [(23, 5)]
private abbrev coordinateInput11_32 : LowerPair × Bool × Bool := (([3], [2]), true, false)
private def coordinateCodes11_32 : List (ℕ × ℕ) := [(16, 0), (16, 3), (16, 0), (17, 0)]
private abbrev coordinateInput11_33 : LowerPair × Bool × Bool := (([3], [2]), false, false)
private def coordinateCodes11_33 : List (ℕ × ℕ) := [(18, 5)]
private abbrev coordinateInput11_34 : LowerPair × Bool × Bool := (([3, 1], [2]), true, false)
private def coordinateCodes11_34 : List (ℕ × ℕ) := [(19, 0), (19, 3), (19, 0), (20, 0), (19, 0)]
private abbrev coordinateInput11_35 : LowerPair × Bool × Bool := (([3, 2], [2]), false, false)
private def coordinateCodes11_35 : List (ℕ × ℕ) := [(21, 5), (21, 5), (21, 10), (21, 5), (24, 5)]
private abbrev coordinateInput11_36 : LowerPair × Bool × Bool := (([3, 2], [2]), true, false)
private def coordinateCodes11_36 : List (ℕ × ℕ) := [(17, 0), (17, 3), (17, 0), (22, 0), (17, 0)]
private abbrev coordinateInput11_37 : LowerPair × Bool × Bool := (([3, 1], [2]), false, false)
private def coordinateCodes11_37 : List (ℕ × ℕ) := [(18, 5), (18, 5)]
private abbrev coordinateInput11_38 : LowerPair × Bool × Bool := (([3], [2, 1]), true, true)
private def coordinateCodes11_38 : List (ℕ × ℕ) := [(16, 12), (16, 12), (16, 13), (16, 12), (17, 12)]
private abbrev coordinateInput11_39 : LowerPair × Bool × Bool := (([3], [2, 2]), false, true)
private def coordinateCodes11_39 : List (ℕ × ℕ) := [(18, 14), (18, 14)]
private abbrev coordinateInput11_40 : LowerPair × Bool × Bool := (([3], [2, 2]), true, true)
private def coordinateCodes11_40 : List (ℕ × ℕ) := [(16, 3), (16, 3), (16, 15), (16, 3), (17, 3)]
private abbrev coordinateInput11_41 : LowerPair × Bool × Bool := (([3], [2, 1]), false, true)
private def coordinateCodes11_41 : List (ℕ × ℕ) := [(18, 5), (18, 5)]
private abbrev coordinateInput11_42 : LowerPair × Bool × Bool := (([2], [2]), true, false)
private def coordinateCodes11_42 : List (ℕ × ℕ) := [(0, 0), (0, 3), (0, 0), (3, 0)]
private abbrev coordinateInput11_43 : LowerPair × Bool × Bool := (([2], [2]), false, false)
private def coordinateCodes11_43 : List (ℕ × ℕ) := [(5, 5), (5, 10), (5, 5), (10, 5)]
private abbrev coordinateInput11_44 : LowerPair × Bool × Bool := (([2, 1], [2]), true, false)
private def coordinateCodes11_44 : List (ℕ × ℕ) := [(12, 0), (12, 3), (12, 0), (13, 0), (12, 0)]
private abbrev coordinateInput11_45 : LowerPair × Bool × Bool := (([2, 2], [2]), false, false)
private def coordinateCodes11_45 : List (ℕ × ℕ) := [(14, 5), (14, 5), (14, 10), (14, 5), (25, 5)]
private abbrev coordinateInput11_46 : LowerPair × Bool × Bool := (([2, 2], [2]), true, false)
private def coordinateCodes11_46 : List (ℕ × ℕ) := [(3, 0), (3, 3), (3, 0), (15, 0), (3, 0)]
private abbrev coordinateInput11_47 : LowerPair × Bool × Bool := (([2, 1], [2]), false, false)
private def coordinateCodes11_47 : List (ℕ × ℕ) := [(5, 5), (5, 5), (5, 10), (5, 5), (10, 5)]
private abbrev coordinateInput11_48 : LowerPair × Bool × Bool := (([2], [2, 1]), true, true)
private def coordinateCodes11_48 : List (ℕ × ℕ) := [(0, 12), (0, 12), (0, 13), (0, 12), (3, 12)]
private abbrev coordinateInput11_49 : LowerPair × Bool × Bool := (([2], [2, 2]), false, true)
private def coordinateCodes11_49 : List (ℕ × ℕ) := [(5, 14), (5, 25), (5, 14), (10, 14), (5, 14)]
private abbrev coordinateInput11_50 : LowerPair × Bool × Bool := (([2], [2, 2]), true, true)
private def coordinateCodes11_50 : List (ℕ × ℕ) := [(0, 3), (0, 3), (0, 15), (0, 3), (3, 3)]
private abbrev coordinateInput11_51 : LowerPair × Bool × Bool := (([2], [2, 1]), false, true)
private def coordinateCodes11_51 : List (ℕ × ℕ) := [(5, 5), (5, 10), (5, 5), (10, 5), (5, 5)]
private abbrev coordinateInput11_52 : LowerPair × Bool × Bool := (([2], [1]), true, false)
private def coordinateCodes11_52 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 1), (3, 1)]
private abbrev coordinateInput11_53 : LowerPair × Bool × Bool := (([2], [1]), false, false)
private def coordinateCodes11_53 : List (ℕ × ℕ) := [(5, 4), (5, 11), (5, 4), (10, 4)]
private abbrev coordinateInput11_54 : LowerPair × Bool × Bool := (([2, 1], [1]), true, false)
private def coordinateCodes11_54 : List (ℕ × ℕ) := [(12, 1), (12, 2), (12, 1), (13, 1), (12, 1)]
private abbrev coordinateInput11_55 : LowerPair × Bool × Bool := (([2, 2], [1]), false, false)
private def coordinateCodes11_55 : List (ℕ × ℕ) := [(14, 4), (14, 4), (14, 11), (14, 4), (25, 4)]
private abbrev coordinateInput11_56 : LowerPair × Bool × Bool := (([2, 2], [1]), true, false)
private def coordinateCodes11_56 : List (ℕ × ℕ) := [(3, 1), (3, 2), (3, 1), (15, 1), (3, 1)]
private abbrev coordinateInput11_57 : LowerPair × Bool × Bool := (([2, 1], [1]), false, false)
private def coordinateCodes11_57 : List (ℕ × ℕ) := [(5, 4), (5, 4), (5, 11), (5, 4), (10, 4)]
private abbrev coordinateInput11_58 : LowerPair × Bool × Bool := (([2], [1, 1]), true, true)
private def coordinateCodes11_58 : List (ℕ × ℕ) := [(0, 6), (0, 6), (0, 7), (0, 6), (3, 6)]
private abbrev coordinateInput11_59 : LowerPair × Bool × Bool := (([2], [1, 2]), false, true)
private def coordinateCodes11_59 : List (ℕ × ℕ) := [(5, 8), (5, 26), (5, 8), (10, 8), (5, 8)]
private abbrev coordinateInput11_60 : LowerPair × Bool × Bool := (([2], [1, 2]), true, true)
private def coordinateCodes11_60 : List (ℕ × ℕ) := [(0, 2), (0, 2), (0, 9), (0, 2), (3, 2)]
private abbrev coordinateInput11_61 : LowerPair × Bool × Bool := (([2], [1, 1]), false, true)
private def coordinateCodes11_61 : List (ℕ × ℕ) := [(5, 4), (5, 11), (5, 4), (10, 4), (5, 4)]
private abbrev coordinateInput11_62 : LowerPair × Bool × Bool := (([3], [1]), true, false)
private def coordinateCodes11_62 : List (ℕ × ℕ) := [(16, 1), (16, 2), (16, 1), (17, 1)]
private abbrev coordinateInput11_63 : LowerPair × Bool × Bool := (([3], [1]), false, false)
private def coordinateCodes11_63 : List (ℕ × ℕ) := [(18, 4)]
private abbrev coordinateInput11_64 : LowerPair × Bool × Bool := (([3, 1], [1]), true, false)
private def coordinateCodes11_64 : List (ℕ × ℕ) := [(19, 1), (19, 2), (19, 1), (20, 1), (19, 1)]
private abbrev coordinateInput11_65 : LowerPair × Bool × Bool := (([3, 2], [1]), false, false)
private def coordinateCodes11_65 : List (ℕ × ℕ) := [(21, 4), (21, 4), (21, 11), (21, 4), (24, 4)]
private abbrev coordinateInput11_66 : LowerPair × Bool × Bool := (([3, 2], [1]), true, false)
private def coordinateCodes11_66 : List (ℕ × ℕ) := [(17, 1), (17, 2), (17, 1), (22, 1), (17, 1)]
private abbrev coordinateInput11_67 : LowerPair × Bool × Bool := (([3, 1], [1]), false, false)
private def coordinateCodes11_67 : List (ℕ × ℕ) := [(18, 4), (18, 4)]
private abbrev coordinateInput11_68 : LowerPair × Bool × Bool := (([3], [1, 1]), true, true)
private def coordinateCodes11_68 : List (ℕ × ℕ) := [(16, 6), (16, 6), (16, 7), (16, 6), (17, 6)]
private abbrev coordinateInput11_69 : LowerPair × Bool × Bool := (([3], [1, 2]), false, true)
private def coordinateCodes11_69 : List (ℕ × ℕ) := [(18, 8), (18, 8)]
private abbrev coordinateInput11_70 : LowerPair × Bool × Bool := (([3], [1, 2]), true, true)
private def coordinateCodes11_70 : List (ℕ × ℕ) := [(16, 2), (16, 2), (16, 9), (16, 2), (17, 2)]
private abbrev coordinateInput11_71 : LowerPair × Bool × Bool := (([3], [1, 1]), false, true)
private def coordinateCodes11_71 : List (ℕ × ℕ) := [(18, 4), (18, 4)]
private abbrev coordinateInput11_72 : LowerPair × Bool × Bool := (([2], [3]), true, false)
private def coordinateCodes11_72 : List (ℕ × ℕ) := [(0, 16), (0, 17), (0, 16), (3, 16)]
private abbrev coordinateInput11_73 : LowerPair × Bool × Bool := (([2], [3]), false, false)
private def coordinateCodes11_73 : List (ℕ × ℕ) := [(5, 18)]
private abbrev coordinateInput11_74 : LowerPair × Bool × Bool := (([2, 1], [3]), true, false)
private def coordinateCodes11_74 : List (ℕ × ℕ) := [(12, 16), (12, 17), (12, 16), (13, 16), (12, 16)]
private abbrev coordinateInput11_75 : LowerPair × Bool × Bool := (([2, 2], [3]), false, false)
private def coordinateCodes11_75 : List (ℕ × ℕ) := [(14, 18), (14, 18)]
private abbrev coordinateInput11_76 : LowerPair × Bool × Bool := (([2, 2], [3]), true, false)
private def coordinateCodes11_76 : List (ℕ × ℕ) := [(3, 16), (3, 17), (3, 16), (15, 16), (3, 16)]
private abbrev coordinateInput11_77 : LowerPair × Bool × Bool := (([2, 1], [3]), false, false)
private def coordinateCodes11_77 : List (ℕ × ℕ) := [(5, 18), (5, 18)]
private abbrev coordinateInput11_78 : LowerPair × Bool × Bool := (([2], [3, 1]), true, true)
private def coordinateCodes11_78 : List (ℕ × ℕ) := [(0, 19), (0, 19), (0, 20), (0, 19), (3, 19)]
private abbrev coordinateInput11_79 : LowerPair × Bool × Bool := (([2], [3, 2]), false, true)
private def coordinateCodes11_79 : List (ℕ × ℕ) := [(5, 21), (5, 24), (5, 21), (10, 21), (5, 21)]
private abbrev coordinateInput11_80 : LowerPair × Bool × Bool := (([2], [3, 2]), true, true)
private def coordinateCodes11_80 : List (ℕ × ℕ) := [(0, 17), (0, 17), (0, 22), (0, 17), (3, 17)]
private abbrev coordinateInput11_81 : LowerPair × Bool × Bool := (([2], [3, 1]), false, true)
private def coordinateCodes11_81 : List (ℕ × ℕ) := [(5, 18), (5, 18)]
private abbrev coordinateInput11_82 : LowerPair × Bool × Bool := (([3], [1, 1]), true, false)
private def coordinateCodes11_82 : List (ℕ × ℕ) := [(16, 6), (16, 6), (16, 7), (16, 6), (17, 6)]
private abbrev coordinateInput11_83 : LowerPair × Bool × Bool := (([3], [1, 1]), false, false)
private def coordinateCodes11_83 : List (ℕ × ℕ) := [(18, 4), (18, 4)]
private abbrev coordinateInput11_84 : LowerPair × Bool × Bool := (([3, 1], [1, 1]), true, false)
private def coordinateCodes11_84 : List (ℕ × ℕ) := [(19, 6), (19, 7), (19, 6), (20, 6)]
private abbrev coordinateInput11_85 : LowerPair × Bool × Bool := (([3, 2], [1, 1]), false, false)
private def coordinateCodes11_85 : List (ℕ × ℕ) := [(21, 4), (21, 11), (21, 4), (24, 4)]
private abbrev coordinateInput11_86 : LowerPair × Bool × Bool := (([3, 2], [1, 1]), true, false)
private def coordinateCodes11_86 : List (ℕ × ℕ) := [(17, 6), (17, 7), (17, 6), (22, 6)]
private abbrev coordinateInput11_87 : LowerPair × Bool × Bool := (([3, 1], [1, 1]), false, false)
private def coordinateCodes11_87 : List (ℕ × ℕ) := [(18, 4)]
private abbrev coordinateInput11_88 : LowerPair × Bool × Bool := (([3], [1, 1, 1]), true, true)
private def coordinateCodes11_88 : List (ℕ × ℕ) := [(16, 6), (16, 7), (16, 6), (17, 6)]
private abbrev coordinateInput11_89 : LowerPair × Bool × Bool := (([3], [1, 1, 2]), false, true)
private def coordinateCodes11_89 : List (ℕ × ℕ) := [(18, 11)]
private abbrev coordinateInput11_90 : LowerPair × Bool × Bool := (([3], [1, 1, 2]), true, true)
private def coordinateCodes11_90 : List (ℕ × ℕ) := [(16, 27), (16, 28), (16, 27), (17, 27)]
private abbrev coordinateInput11_91 : LowerPair × Bool × Bool := (([3], [1, 1, 1]), false, true)
private def coordinateCodes11_91 : List (ℕ × ℕ) := [(18, 29)]

private def decodeCoordinate11 (x : ℕ × ℕ) : CertField × CertField :=
  (coordinateFields11[x.1]?.getD ⟨0,0,0,0⟩,coordinateFields11[x.2]?.getD ⟨0,0,0,0⟩)

private theorem hCoordinate11_0 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_0.1 coordinateInput11_0.2.1 coordinateInput11_0.2.2).map Prod.fst = coordinateCodes11_0.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_1 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_1.1 coordinateInput11_1.2.1 coordinateInput11_1.2.2).map Prod.fst = coordinateCodes11_1.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_2 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_2.1 coordinateInput11_2.2.1 coordinateInput11_2.2.2).map Prod.fst = coordinateCodes11_2.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_3 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_3.1 coordinateInput11_3.2.1 coordinateInput11_3.2.2).map Prod.fst = coordinateCodes11_3.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_4 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_4.1 coordinateInput11_4.2.1 coordinateInput11_4.2.2).map Prod.fst = coordinateCodes11_4.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_5 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_5.1 coordinateInput11_5.2.1 coordinateInput11_5.2.2).map Prod.fst = coordinateCodes11_5.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_6 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_6.1 coordinateInput11_6.2.1 coordinateInput11_6.2.2).map Prod.fst = coordinateCodes11_6.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_7 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_7.1 coordinateInput11_7.2.1 coordinateInput11_7.2.2).map Prod.fst = coordinateCodes11_7.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_8 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_8.1 coordinateInput11_8.2.1 coordinateInput11_8.2.2).map Prod.fst = coordinateCodes11_8.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_9 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_9.1 coordinateInput11_9.2.1 coordinateInput11_9.2.2).map Prod.fst = coordinateCodes11_9.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_10 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_10.1 coordinateInput11_10.2.1 coordinateInput11_10.2.2).map Prod.fst = coordinateCodes11_10.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_11 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_11.1 coordinateInput11_11.2.1 coordinateInput11_11.2.2).map Prod.fst = coordinateCodes11_11.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_12 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_12.1 coordinateInput11_12.2.1 coordinateInput11_12.2.2).map Prod.fst = coordinateCodes11_12.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_13 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_13.1 coordinateInput11_13.2.1 coordinateInput11_13.2.2).map Prod.fst = coordinateCodes11_13.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_14 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_14.1 coordinateInput11_14.2.1 coordinateInput11_14.2.2).map Prod.fst = coordinateCodes11_14.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_15 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_15.1 coordinateInput11_15.2.1 coordinateInput11_15.2.2).map Prod.fst = coordinateCodes11_15.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_16 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_16.1 coordinateInput11_16.2.1 coordinateInput11_16.2.2).map Prod.fst = coordinateCodes11_16.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_17 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_17.1 coordinateInput11_17.2.1 coordinateInput11_17.2.2).map Prod.fst = coordinateCodes11_17.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_18 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_18.1 coordinateInput11_18.2.1 coordinateInput11_18.2.2).map Prod.fst = coordinateCodes11_18.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_19 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_19.1 coordinateInput11_19.2.1 coordinateInput11_19.2.2).map Prod.fst = coordinateCodes11_19.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_20 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_20.1 coordinateInput11_20.2.1 coordinateInput11_20.2.2).map Prod.fst = coordinateCodes11_20.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_21 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_21.1 coordinateInput11_21.2.1 coordinateInput11_21.2.2).map Prod.fst = coordinateCodes11_21.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_22 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_22.1 coordinateInput11_22.2.1 coordinateInput11_22.2.2).map Prod.fst = coordinateCodes11_22.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_23 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_23.1 coordinateInput11_23.2.1 coordinateInput11_23.2.2).map Prod.fst = coordinateCodes11_23.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_24 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_24.1 coordinateInput11_24.2.1 coordinateInput11_24.2.2).map Prod.fst = coordinateCodes11_24.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_25 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_25.1 coordinateInput11_25.2.1 coordinateInput11_25.2.2).map Prod.fst = coordinateCodes11_25.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_26 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_26.1 coordinateInput11_26.2.1 coordinateInput11_26.2.2).map Prod.fst = coordinateCodes11_26.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_27 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_27.1 coordinateInput11_27.2.1 coordinateInput11_27.2.2).map Prod.fst = coordinateCodes11_27.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_28 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_28.1 coordinateInput11_28.2.1 coordinateInput11_28.2.2).map Prod.fst = coordinateCodes11_28.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_29 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_29.1 coordinateInput11_29.2.1 coordinateInput11_29.2.2).map Prod.fst = coordinateCodes11_29.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_30 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_30.1 coordinateInput11_30.2.1 coordinateInput11_30.2.2).map Prod.fst = coordinateCodes11_30.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_31 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_31.1 coordinateInput11_31.2.1 coordinateInput11_31.2.2).map Prod.fst = coordinateCodes11_31.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_32 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_32.1 coordinateInput11_32.2.1 coordinateInput11_32.2.2).map Prod.fst = coordinateCodes11_32.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_33 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_33.1 coordinateInput11_33.2.1 coordinateInput11_33.2.2).map Prod.fst = coordinateCodes11_33.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_34 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_34.1 coordinateInput11_34.2.1 coordinateInput11_34.2.2).map Prod.fst = coordinateCodes11_34.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_35 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_35.1 coordinateInput11_35.2.1 coordinateInput11_35.2.2).map Prod.fst = coordinateCodes11_35.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_36 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_36.1 coordinateInput11_36.2.1 coordinateInput11_36.2.2).map Prod.fst = coordinateCodes11_36.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_37 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_37.1 coordinateInput11_37.2.1 coordinateInput11_37.2.2).map Prod.fst = coordinateCodes11_37.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_38 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_38.1 coordinateInput11_38.2.1 coordinateInput11_38.2.2).map Prod.fst = coordinateCodes11_38.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_39 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_39.1 coordinateInput11_39.2.1 coordinateInput11_39.2.2).map Prod.fst = coordinateCodes11_39.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_40 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_40.1 coordinateInput11_40.2.1 coordinateInput11_40.2.2).map Prod.fst = coordinateCodes11_40.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_41 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_41.1 coordinateInput11_41.2.1 coordinateInput11_41.2.2).map Prod.fst = coordinateCodes11_41.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_42 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_42.1 coordinateInput11_42.2.1 coordinateInput11_42.2.2).map Prod.fst = coordinateCodes11_42.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_43 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_43.1 coordinateInput11_43.2.1 coordinateInput11_43.2.2).map Prod.fst = coordinateCodes11_43.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_44 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_44.1 coordinateInput11_44.2.1 coordinateInput11_44.2.2).map Prod.fst = coordinateCodes11_44.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_45 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_45.1 coordinateInput11_45.2.1 coordinateInput11_45.2.2).map Prod.fst = coordinateCodes11_45.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_46 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_46.1 coordinateInput11_46.2.1 coordinateInput11_46.2.2).map Prod.fst = coordinateCodes11_46.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_47 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_47.1 coordinateInput11_47.2.1 coordinateInput11_47.2.2).map Prod.fst = coordinateCodes11_47.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_48 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_48.1 coordinateInput11_48.2.1 coordinateInput11_48.2.2).map Prod.fst = coordinateCodes11_48.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_49 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_49.1 coordinateInput11_49.2.1 coordinateInput11_49.2.2).map Prod.fst = coordinateCodes11_49.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_50 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_50.1 coordinateInput11_50.2.1 coordinateInput11_50.2.2).map Prod.fst = coordinateCodes11_50.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_51 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_51.1 coordinateInput11_51.2.1 coordinateInput11_51.2.2).map Prod.fst = coordinateCodes11_51.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_52 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_52.1 coordinateInput11_52.2.1 coordinateInput11_52.2.2).map Prod.fst = coordinateCodes11_52.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_53 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_53.1 coordinateInput11_53.2.1 coordinateInput11_53.2.2).map Prod.fst = coordinateCodes11_53.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_54 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_54.1 coordinateInput11_54.2.1 coordinateInput11_54.2.2).map Prod.fst = coordinateCodes11_54.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_55 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_55.1 coordinateInput11_55.2.1 coordinateInput11_55.2.2).map Prod.fst = coordinateCodes11_55.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_56 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_56.1 coordinateInput11_56.2.1 coordinateInput11_56.2.2).map Prod.fst = coordinateCodes11_56.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_57 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_57.1 coordinateInput11_57.2.1 coordinateInput11_57.2.2).map Prod.fst = coordinateCodes11_57.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_58 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_58.1 coordinateInput11_58.2.1 coordinateInput11_58.2.2).map Prod.fst = coordinateCodes11_58.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_59 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_59.1 coordinateInput11_59.2.1 coordinateInput11_59.2.2).map Prod.fst = coordinateCodes11_59.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_60 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_60.1 coordinateInput11_60.2.1 coordinateInput11_60.2.2).map Prod.fst = coordinateCodes11_60.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_61 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_61.1 coordinateInput11_61.2.1 coordinateInput11_61.2.2).map Prod.fst = coordinateCodes11_61.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_62 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_62.1 coordinateInput11_62.2.1 coordinateInput11_62.2.2).map Prod.fst = coordinateCodes11_62.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_63 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_63.1 coordinateInput11_63.2.1 coordinateInput11_63.2.2).map Prod.fst = coordinateCodes11_63.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_64 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_64.1 coordinateInput11_64.2.1 coordinateInput11_64.2.2).map Prod.fst = coordinateCodes11_64.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_65 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_65.1 coordinateInput11_65.2.1 coordinateInput11_65.2.2).map Prod.fst = coordinateCodes11_65.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_66 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_66.1 coordinateInput11_66.2.1 coordinateInput11_66.2.2).map Prod.fst = coordinateCodes11_66.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_67 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_67.1 coordinateInput11_67.2.1 coordinateInput11_67.2.2).map Prod.fst = coordinateCodes11_67.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_68 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_68.1 coordinateInput11_68.2.1 coordinateInput11_68.2.2).map Prod.fst = coordinateCodes11_68.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_69 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_69.1 coordinateInput11_69.2.1 coordinateInput11_69.2.2).map Prod.fst = coordinateCodes11_69.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_70 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_70.1 coordinateInput11_70.2.1 coordinateInput11_70.2.2).map Prod.fst = coordinateCodes11_70.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_71 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_71.1 coordinateInput11_71.2.1 coordinateInput11_71.2.2).map Prod.fst = coordinateCodes11_71.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_72 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_72.1 coordinateInput11_72.2.1 coordinateInput11_72.2.2).map Prod.fst = coordinateCodes11_72.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_73 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_73.1 coordinateInput11_73.2.1 coordinateInput11_73.2.2).map Prod.fst = coordinateCodes11_73.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_74 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_74.1 coordinateInput11_74.2.1 coordinateInput11_74.2.2).map Prod.fst = coordinateCodes11_74.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_75 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_75.1 coordinateInput11_75.2.1 coordinateInput11_75.2.2).map Prod.fst = coordinateCodes11_75.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_76 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_76.1 coordinateInput11_76.2.1 coordinateInput11_76.2.2).map Prod.fst = coordinateCodes11_76.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_77 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_77.1 coordinateInput11_77.2.1 coordinateInput11_77.2.2).map Prod.fst = coordinateCodes11_77.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_78 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_78.1 coordinateInput11_78.2.1 coordinateInput11_78.2.2).map Prod.fst = coordinateCodes11_78.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_79 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_79.1 coordinateInput11_79.2.1 coordinateInput11_79.2.2).map Prod.fst = coordinateCodes11_79.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_80 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_80.1 coordinateInput11_80.2.1 coordinateInput11_80.2.2).map Prod.fst = coordinateCodes11_80.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_81 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_81.1 coordinateInput11_81.2.1 coordinateInput11_81.2.2).map Prod.fst = coordinateCodes11_81.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_82 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_82.1 coordinateInput11_82.2.1 coordinateInput11_82.2.2).map Prod.fst = coordinateCodes11_82.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_83 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_83.1 coordinateInput11_83.2.1 coordinateInput11_83.2.2).map Prod.fst = coordinateCodes11_83.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_84 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_84.1 coordinateInput11_84.2.1 coordinateInput11_84.2.2).map Prod.fst = coordinateCodes11_84.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_85 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_85.1 coordinateInput11_85.2.1 coordinateInput11_85.2.2).map Prod.fst = coordinateCodes11_85.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_86 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_86.1 coordinateInput11_86.2.1 coordinateInput11_86.2.2).map Prod.fst = coordinateCodes11_86.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_87 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_87.1 coordinateInput11_87.2.1 coordinateInput11_87.2.2).map Prod.fst = coordinateCodes11_87.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_88 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_88.1 coordinateInput11_88.2.1 coordinateInput11_88.2.2).map Prod.fst = coordinateCodes11_88.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_89 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_89.1 coordinateInput11_89.2.1 coordinateInput11_89.2.2).map Prod.fst = coordinateCodes11_89.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_90 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_90.1 coordinateInput11_90.2.1 coordinateInput11_90.2.2).map Prod.fst = coordinateCodes11_90.map decodeCoordinate11 := by decide +kernel

private theorem hCoordinate11_91 :
    (trunkEndpointCases (trunkCatalog.states 11).context coordinateInput11_91.1 coordinateInput11_91.2.1 coordinateInput11_91.2.2).map Prod.fst = coordinateCodes11_91.map decodeCoordinate11 := by decide +kernel

private def parentsForAll (keys : List CoverageKey) (plan goal : ℕ)
    (branches : List (ℕ × Bool)) : List ℕ :=
  keys.flatMap fun g =>
    if g.1 = plan ∧ g.2.2.1 = goal ∧
        ∀ ba ∈ branches, ba.2 = true ∨ (ba.1 : ℤ) ∈ g.2.2.2
    then g.2.1 else []

private theorem parentsForAll_sound (keys : List CoverageKey) (plan parent goal : ℕ)
    (branches : List (ℕ × Bool)) (ba : ℕ × Bool)
    (hp : parent ∈ parentsForAll keys plan goal branches) (hb : ba ∈ branches) :
    ba.2 = true ∨ coverageKeyRecorded keys plan parent goal ba.1 := by
  obtain ⟨g,hg,hm⟩ := List.mem_flatMap.mp hp
  split at hm
  next hc =>
    rcases hc.2.2 ba hb with ha | hbr
    · exact Or.inl ha
    · exact Or.inr ⟨g,hg,hc.1,hm,hc.2.1,hbr⟩
  next hc => simp at hm

private def coverageRemainder (keys : List CoverageKey) (tasks : List CoverageTask)
    (parents : ℕ) (remainders : List (List ℕ)) : Prop :=
  ∀ pg ∈ tasks,
    (List.range parents).Sublist (sortFuel 12 (parentsFor keys pg.1 0 (-1) ++ remainders[pg.1]?.getD [])) ∧
    ∀ gb ∈ pg.2,
      (∀ ba ∈ gb.2, ba.2 = true) ∨ (remainders[pg.1]?.getD []).Sublist
        (sortFuel 12 (parentsForAll keys pg.1 gb.1 gb.2))

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
    rcases (h pg hpg).2 gb hgb with ha | hs
    · exact Or.inl (ha ba hba)
    · apply parentsForAll_sound keys pg.1 par gb.1 gb.2 ba _ hba
      simpa only [mem_sortFuel] using hs.subset hp

private def checkedKeys : List CoverageKey := [(0,[0],0,[-1]),
(0,[1,5,6,10,12,16,18,22,24,28],0,[-1]),
(0,[2,3,8,9,14,15,20,21,26,27],0,[-1]),
(0,[4],0,[-1]),
(0,[7],2,[0,1,2,3]),
(0,[7,13],5,[0,1,2,3]),
(0,[7,13],7,[0,1,2,3]),
(0,[7],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[7],12,[0,1,2,3]),
(0,[7],15,[0,1,2,3]),
(0,[7],17,[0,1,2,3,4,5,6,7,8,9]),
(0,[7],19,[0,1,2,3,4,5,6,7,8,9]),
(0,[11],0,[-1]),
(0,[13],2,[0,1,2,3]),
(0,[13],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[13],12,[0,1,2,3]),
(0,[13],15,[0,1,2,3]),
(0,[13],17,[0,1,2,3,4,5,6,7,8,9]),
(0,[13],19,[0,1,2,3,4,5,6,7,8,9]),
(0,[17],0,[-1]),
(0,[19,23],0,[-1]),
(0,[25,29],0,[-1]),
(1,[0,4],0,[-1]),
(1,[1,5,6,10,12,16,18,22,24,28],0,[-1]),
(1,[2,3,8,9,14,15,20,21,26,27],0,[-1]),
(1,[7,11],0,[-1]),
(1,[13,19,25],0,[-1]),
(1,[17],0,[-1]),
(1,[23],0,[-1]),
(1,[29],0,[-1]),
(2,[0],0,[-1]),
(2,[1,5,6,10,12,16,18,22,24,28],0,[-1]),
(2,[2,3,8,9,14,15,20,21,26,27],0,[-1]),
(2,[4],0,[-1]),
(2,[7],0,[-1]),
(2,[11],0,[-1]),
(2,[13],2,[0,1,2,3]),
(2,[13],5,[0,1,2,3]),
(2,[13,17,23,29],7,[0,1,2,3]),
(2,[13],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[13],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[13],14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[13],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[13],19,[0,1,2,3,4,5,6,7,8,9]),
(2,[13],22,[0,1,2,3,4,5,6,7,8,9]),
(2,[17,23,29],2,[0,1,2,3]),
(2,[17],5,[0,1,2,3]),
(2,[17],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[17],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[17],14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[17],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[17],19,[0,1,2,3,4,5,6,7,8,9]),
(2,[17],22,[0,1,2,3,4,5,6,7,8,9]),
(2,[19],0,[-1]),
(2,[23],5,[0,1,2,3]),
(2,[23],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[23],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[23],14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[23],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[23],19,[0,1,2,3,4,5,6,7,8,9]),
(2,[23],22,[0,1,2,3,4,5,6,7,8,9]),
(2,[25],0,[-1]),
(2,[29],5,[0,1,2,3]),
(2,[29],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[29],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[29],14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[29],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[29],19,[0,1,2,3,4,5,6,7,8,9]),
(2,[29],22,[0,1,2,3,4,5,6,7,8,9]),
(3,[0,4],0,[-1]),
(3,[1,5,6,10,12,16,18,22,24,28],0,[-1]),
(3,[2,3,8,9,14,15,20,21,26,27],0,[-1]),
(3,[7,11],0,[-1]),
(3,[13,19,25],0,[-1]),
(3,[17],0,[-1]),
(3,[23],2,[0,1,2,3]),
(3,[23],5,[0,1,2,3]),
(3,[23],7,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[23],9,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[23],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[23],14,[0,1,2,3,4,5,6,7,8,9]),
(3,[23],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[23],19,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[23],22,[0,1,2,3,4,5,6,7,8,9]),
(3,[23],24,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[23],27,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[23],29,[0,1,2,3,4,5,6,7,8,9]),
(3,[23],32,[0,1,2,3,4,5,6,7]),
(3,[23],34,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[23],35,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[23],36,[0,1,2,3]),
(3,[23],38,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[23],39,[0,1,2,3]),
(3,[23],40,[0,1,2,3]),
(3,[29],0,[-1]),
(4,[0,4],0,[-1]),
(4,[1,5,6,10,12,16,18,22,24,28],0,[-1]),
(4,[2,3,8,9,14,15,20,21,26,27],0,[-1]),
(4,[7,11],0,[-1]),
(4,[13,19,25],0,[-1]),
(4,[17],0,[-1]),
(4,[23],2,[0,1,2,3]),
(4,[23],5,[0,1,2,3]),
(4,[23],7,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[23],9,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[23],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(4,[23],15,[0,1,2,3]),
(4,[23],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[23],19,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[23],22,[0,1,2,3,4,5,6,7,8,9]),
(4,[23],24,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[23],27,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[23],29,[0,1,2,3,4,5,6,7,8,9]),
(4,[23],32,[0,1,2,3,4,5,6,7]),
(4,[23],34,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]),
(4,[23],35,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]),
(4,[23],36,[0,1,2,3,4,5,6,7]),
(4,[23],38,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(4,[23],39,[0,1,2,3]),
(4,[23],40,[0,1,2,3]),
(4,[29],0,[-1])]
private def checkedTasks : List CoverageTask := [(0,[(1, (List.replicate 4 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 4 false).zipIdx.map Prod.swap),(6, (List.replicate 10 true).zipIdx.map Prod.swap),(7, (List.replicate 4 false).zipIdx.map Prod.swap),(8, (List.replicate 4 true).zipIdx.map Prod.swap),(9, (List.replicate 16 true).zipIdx.map Prod.swap),(10, (List.replicate 16 false).zipIdx.map Prod.swap),(11, (List.replicate 10 true).zipIdx.map Prod.swap),(12, (List.replicate 4 false).zipIdx.map Prod.swap),(13, (List.replicate 4 true).zipIdx.map Prod.swap),(14, (List.replicate 4 true).zipIdx.map Prod.swap),(15, (List.replicate 4 false).zipIdx.map Prod.swap),(16, (List.replicate 4 true).zipIdx.map Prod.swap),(17, (List.replicate 10 false).zipIdx.map Prod.swap),(18, (List.replicate 10 true).zipIdx.map Prod.swap),(19, (List.replicate 10 false).zipIdx.map Prod.swap),(20, (List.replicate 2 true).zipIdx.map Prod.swap),(21, (List.replicate 2 true).zipIdx.map Prod.swap)]),(1,[(1, (List.replicate 4 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 4 false).zipIdx.map Prod.swap),(6, (List.replicate 10 true).zipIdx.map Prod.swap),(7, (List.replicate 4 false).zipIdx.map Prod.swap),(8, (List.replicate 4 true).zipIdx.map Prod.swap),(9, (List.replicate 16 true).zipIdx.map Prod.swap),(10, (List.replicate 16 false).zipIdx.map Prod.swap),(11, (List.replicate 4 true).zipIdx.map Prod.swap),(12, (List.replicate 25 false).zipIdx.map Prod.swap),(13, (List.replicate 10 true).zipIdx.map Prod.swap),(14, (List.replicate 10 false).zipIdx.map Prod.swap),(15, (List.replicate 10 true).zipIdx.map Prod.swap),(16, (List.replicate 4 true).zipIdx.map Prod.swap),(17, (List.replicate 10 false).zipIdx.map Prod.swap),(18, (List.replicate 5 true).zipIdx.map Prod.swap),(19, (List.replicate 8 false).zipIdx.map Prod.swap),(20, (List.replicate 2 true).zipIdx.map Prod.swap),(21, (List.replicate 1 true).zipIdx.map Prod.swap)]),(2,[(1, (List.replicate 4 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 4 false).zipIdx.map Prod.swap),(6, (List.replicate 10 true).zipIdx.map Prod.swap),(7, (List.replicate 4 false).zipIdx.map Prod.swap),(8, (List.replicate 4 true).zipIdx.map Prod.swap),(9, (List.replicate 16 true).zipIdx.map Prod.swap),(10, (List.replicate 16 false).zipIdx.map Prod.swap),(11, (List.replicate 16 true).zipIdx.map Prod.swap),(12, (List.replicate 25 false).zipIdx.map Prod.swap),(13, (List.replicate 25 true).zipIdx.map Prod.swap),(14, (List.replicate 25 false).zipIdx.map Prod.swap),(15, (List.replicate 25 true).zipIdx.map Prod.swap),(16, (List.replicate 4 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 10 true).zipIdx.map Prod.swap),(19, (List.replicate 10 false).zipIdx.map Prod.swap),(20, (List.replicate 10 true).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 20 true).zipIdx.map Prod.swap),(24, (List.replicate 8 true).zipIdx.map Prod.swap),(25, (List.replicate 2 true).zipIdx.map Prod.swap),(26, (List.replicate 1 true).zipIdx.map Prod.swap)]),(3,[(1, (List.replicate 4 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 4 false).zipIdx.map Prod.swap),(6, (List.replicate 16 true).zipIdx.map Prod.swap),(7, (List.replicate 25 false).zipIdx.map Prod.swap),(8, (List.replicate 25 true).zipIdx.map Prod.swap),(9, (List.replicate 25 false).zipIdx.map Prod.swap),(10, (List.replicate 25 true).zipIdx.map Prod.swap),(11, (List.replicate 4 true).zipIdx.map Prod.swap),(12, (List.replicate 25 false).zipIdx.map Prod.swap),(13, (List.replicate 10 true).zipIdx.map Prod.swap),(14, (List.replicate 10 false).zipIdx.map Prod.swap),(15, (List.replicate 10 true).zipIdx.map Prod.swap),(16, (List.replicate 16 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 25 true).zipIdx.map Prod.swap),(19, (List.replicate 25 false).zipIdx.map Prod.swap),(20, (List.replicate 25 true).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 25 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 4 true).zipIdx.map Prod.swap),(27, (List.replicate 25 false).zipIdx.map Prod.swap),(28, (List.replicate 10 true).zipIdx.map Prod.swap),(29, (List.replicate 10 false).zipIdx.map Prod.swap),(30, (List.replicate 10 true).zipIdx.map Prod.swap),(31, (List.replicate 8 true).zipIdx.map Prod.swap),(32, (List.replicate 8 false).zipIdx.map Prod.swap),(33, (List.replicate 4 true).zipIdx.map Prod.swap),(34, (List.replicate 16 false).zipIdx.map Prod.swap),(35, (List.replicate 16 false).zipIdx.map Prod.swap),(36, (List.replicate 4 false).zipIdx.map Prod.swap),(37, (List.replicate 4 true).zipIdx.map Prod.swap),(38, (List.replicate 16 false).zipIdx.map Prod.swap),(39, (List.replicate 4 false).zipIdx.map Prod.swap),(40, (List.replicate 4 false).zipIdx.map Prod.swap),(41, (List.replicate 2 true).zipIdx.map Prod.swap),(42, (List.replicate 1 true).zipIdx.map Prod.swap)]),(4,[(1, (List.replicate 4 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 4 false).zipIdx.map Prod.swap),(6, (List.replicate 16 true).zipIdx.map Prod.swap),(7, (List.replicate 25 false).zipIdx.map Prod.swap),(8, (List.replicate 25 true).zipIdx.map Prod.swap),(9, (List.replicate 25 false).zipIdx.map Prod.swap),(10, (List.replicate 25 true).zipIdx.map Prod.swap),(11, (List.replicate 10 true).zipIdx.map Prod.swap),(12, (List.replicate 16 false).zipIdx.map Prod.swap),(13, (List.replicate 4 true).zipIdx.map Prod.swap),(14, (List.replicate 4 true).zipIdx.map Prod.swap),(15, (List.replicate 4 false).zipIdx.map Prod.swap),(16, (List.replicate 16 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 25 true).zipIdx.map Prod.swap),(19, (List.replicate 25 false).zipIdx.map Prod.swap),(20, (List.replicate 25 true).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 25 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 4 true).zipIdx.map Prod.swap),(27, (List.replicate 25 false).zipIdx.map Prod.swap),(28, (List.replicate 10 true).zipIdx.map Prod.swap),(29, (List.replicate 10 false).zipIdx.map Prod.swap),(30, (List.replicate 10 true).zipIdx.map Prod.swap),(31, (List.replicate 8 true).zipIdx.map Prod.swap),(32, (List.replicate 8 false).zipIdx.map Prod.swap),(33, (List.replicate 8 true).zipIdx.map Prod.swap),(34, (List.replicate 20 false).zipIdx.map Prod.swap),(35, (List.replicate 20 false).zipIdx.map Prod.swap),(36, (List.replicate 8 false).zipIdx.map Prod.swap),(37, (List.replicate 4 true).zipIdx.map Prod.swap),(38, (List.replicate 16 false).zipIdx.map Prod.swap),(39, (List.replicate 4 false).zipIdx.map Prod.swap),(40, (List.replicate 4 false).zipIdx.map Prod.swap),(41, (List.replicate 2 true).zipIdx.map Prod.swap),(42, (List.replicate 1 true).zipIdx.map Prod.swap)])]
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

private theorem automaticFlags_same (C : LowerHistoryContext) (s t : Section14Spec)
    (hl : (s.first,s.firstUpper,trunkSpecIncoming s) = (t.first,t.firstUpper,trunkSpecIncoming t))
    (hr : (s.second,s.secondUpper,trunkSpecIncoming s) = (t.second,t.secondUpper,trunkSpecIncoming t))
    (hs : s.strict = t.strict) : automaticFlags C s = automaticFlags C t := by
  have hL := congrArg (fun x : LowerPair × Bool × Bool =>
    (trunkEndpointCases C x.1 x.2.1 x.2.2).map Prod.fst) hl
  have hR := congrArg (fun x : LowerPair × Bool × Bool =>
    (trunkEndpointCases C x.1 x.2.1 x.2.2).map Prod.fst) hr
  unfold automaticFlags
  rw [hL,hR,hs]
private abbrev specAt11 (pi goal : ℕ) : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) pi))[goal-1]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private abbrev cSpec11_0_1 := specAt11 0 1
private theorem cFlags11_0_1 : automaticFlags (trunkCatalog.states 11).context cSpec11_0_1 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_2 coordinateInput11_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_2 hCoordinate11_1]
  decide +kernel
private abbrev cSpec11_0_2 := specAt11 0 2
private theorem cFlags11_0_2 : automaticFlags (trunkCatalog.states 11).context cSpec11_0_2 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_4 coordinateInput11_5 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_4 hCoordinate11_5]
  decide +kernel
private abbrev cSpec11_0_3 := specAt11 0 3
private theorem cFlags11_0_3 : automaticFlags (trunkCatalog.states 11).context cSpec11_0_3 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_6 coordinateInput11_7 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_6 hCoordinate11_7]
  decide +kernel
private abbrev cSpec11_0_4 := specAt11 0 4
private theorem cFlags11_0_4 : automaticFlags (trunkCatalog.states 11).context cSpec11_0_4 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_8 coordinateInput11_9 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_8 hCoordinate11_9]
  decide +kernel
private abbrev cSpec11_0_5 := specAt11 0 5
private theorem cFlags11_0_5 : automaticFlags (trunkCatalog.states 11).context cSpec11_0_5 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_10 coordinateInput11_11 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_10 hCoordinate11_11]
  decide +kernel
private abbrev cSpec11_0_6 := specAt11 0 6
private theorem cFlags11_0_6 : automaticFlags (trunkCatalog.states 11).context cSpec11_0_6 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_0 coordinateInput11_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_0 hCoordinate11_3]
  decide +kernel
private abbrev cSpec11_0_7 := specAt11 0 7
private theorem cFlags11_0_7 : automaticFlags (trunkCatalog.states 11).context cSpec11_0_7 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_12 coordinateInput11_13 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_12 hCoordinate11_13]
  decide +kernel
private abbrev cSpec11_0_8 := specAt11 0 8
private theorem cFlags11_0_8 : automaticFlags (trunkCatalog.states 11).context cSpec11_0_8 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_14 coordinateInput11_15 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_14 hCoordinate11_15]
  decide +kernel
private abbrev cSpec11_0_9 := specAt11 0 9
private theorem cFlags11_0_9 : automaticFlags (trunkCatalog.states 11).context cSpec11_0_9 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_16 coordinateInput11_17 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_16 hCoordinate11_17]
  decide +kernel
private abbrev cSpec11_0_10 := specAt11 0 10
private theorem cFlags11_0_10 : automaticFlags (trunkCatalog.states 11).context cSpec11_0_10 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_18 coordinateInput11_19 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_18 hCoordinate11_19]
  decide +kernel
private abbrev cSpec11_0_11 := specAt11 0 11
private theorem cFlags11_0_11 : automaticFlags (trunkCatalog.states 11).context cSpec11_0_11 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_20 coordinateInput11_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_20 hCoordinate11_21]
  decide +kernel
private abbrev cSpec11_0_12 := specAt11 0 12
private theorem cFlags11_0_12 : automaticFlags (trunkCatalog.states 11).context cSpec11_0_12 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_22 coordinateInput11_23 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_22 hCoordinate11_23]
  decide +kernel
private abbrev cSpec11_0_13 := specAt11 0 13
private theorem cFlags11_0_13 : automaticFlags (trunkCatalog.states 11).context cSpec11_0_13 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_24 coordinateInput11_25 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_24 hCoordinate11_25]
  decide +kernel
private abbrev cSpec11_0_14 := specAt11 0 14
private theorem cFlags11_0_14 : automaticFlags (trunkCatalog.states 11).context cSpec11_0_14 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_26 coordinateInput11_27 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_26 hCoordinate11_27]
  decide +kernel
private abbrev cSpec11_0_15 := specAt11 0 15
private theorem cFlags11_0_15 : automaticFlags (trunkCatalog.states 11).context cSpec11_0_15 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_28 coordinateInput11_29 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_28 hCoordinate11_29]
  decide +kernel
private abbrev cSpec11_0_16 := specAt11 0 16
private theorem cFlags11_0_16 : automaticFlags (trunkCatalog.states 11).context cSpec11_0_16 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_2 coordinateInput11_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_2 hCoordinate11_3]
  decide +kernel
private abbrev cSpec11_0_17 := specAt11 0 17
private theorem cFlags11_0_17 : automaticFlags (trunkCatalog.states 11).context cSpec11_0_17 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_0 coordinateInput11_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_0 hCoordinate11_1]
  decide +kernel
private abbrev cSpec11_0_18 := specAt11 0 18
private theorem cFlags11_0_18 : automaticFlags (trunkCatalog.states 11).context cSpec11_0_18 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_0 coordinateInput11_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_0 hCoordinate11_21]
  decide +kernel
private abbrev cSpec11_0_19 := specAt11 0 19
private theorem cFlags11_0_19 : automaticFlags (trunkCatalog.states 11).context cSpec11_0_19 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_20 coordinateInput11_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_20 hCoordinate11_3]
  decide +kernel
private abbrev cSpec11_0_20 := specAt11 0 20
private theorem cFlags11_0_20 : automaticFlags (trunkCatalog.states 11).context cSpec11_0_20 = (List.replicate 2 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_2 coordinateInput11_30 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_2 hCoordinate11_30]
  decide +kernel
private abbrev cSpec11_0_21 := specAt11 0 21
private theorem cFlags11_0_21 : automaticFlags (trunkCatalog.states 11).context cSpec11_0_21 = (List.replicate 2 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_31 coordinateInput11_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_31 hCoordinate11_21]
  decide +kernel
private abbrev cSpec11_1_1 := specAt11 1 1
private theorem cFlags11_1_1 : automaticFlags (trunkCatalog.states 11).context cSpec11_1_1 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_1

private abbrev cSpec11_1_2 := specAt11 1 2
private theorem cFlags11_1_2 : automaticFlags (trunkCatalog.states 11).context cSpec11_1_2 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec11_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_2

private abbrev cSpec11_1_3 := specAt11 1 3
private theorem cFlags11_1_3 : automaticFlags (trunkCatalog.states 11).context cSpec11_1_3 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_3

private abbrev cSpec11_1_4 := specAt11 1 4
private theorem cFlags11_1_4 : automaticFlags (trunkCatalog.states 11).context cSpec11_1_4 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_4

private abbrev cSpec11_1_5 := specAt11 1 5
private theorem cFlags11_1_5 : automaticFlags (trunkCatalog.states 11).context cSpec11_1_5 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec11_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_5

private abbrev cSpec11_1_6 := specAt11 1 6
private theorem cFlags11_1_6 : automaticFlags (trunkCatalog.states 11).context cSpec11_1_6 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_6

private abbrev cSpec11_1_7 := specAt11 1 7
private theorem cFlags11_1_7 : automaticFlags (trunkCatalog.states 11).context cSpec11_1_7 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec11_0_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_7

private abbrev cSpec11_1_8 := specAt11 1 8
private theorem cFlags11_1_8 : automaticFlags (trunkCatalog.states 11).context cSpec11_1_8 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_8

private abbrev cSpec11_1_9 := specAt11 1 9
private theorem cFlags11_1_9 : automaticFlags (trunkCatalog.states 11).context cSpec11_1_9 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_9

private abbrev cSpec11_1_10 := specAt11 1 10
private theorem cFlags11_1_10 : automaticFlags (trunkCatalog.states 11).context cSpec11_1_10 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec11_0_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_10

private abbrev cSpec11_1_11 := specAt11 1 11
private theorem cFlags11_1_11 : automaticFlags (trunkCatalog.states 11).context cSpec11_1_11 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_32 coordinateInput11_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_32 hCoordinate11_33]
  decide +kernel
private abbrev cSpec11_1_12 := specAt11 1 12
private theorem cFlags11_1_12 : automaticFlags (trunkCatalog.states 11).context cSpec11_1_12 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_34 coordinateInput11_35 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_34 hCoordinate11_35]
  decide +kernel
private abbrev cSpec11_1_13 := specAt11 1 13
private theorem cFlags11_1_13 : automaticFlags (trunkCatalog.states 11).context cSpec11_1_13 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_36 coordinateInput11_37 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_36 hCoordinate11_37]
  decide +kernel
private abbrev cSpec11_1_14 := specAt11 1 14
private theorem cFlags11_1_14 : automaticFlags (trunkCatalog.states 11).context cSpec11_1_14 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_38 coordinateInput11_39 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_38 hCoordinate11_39]
  decide +kernel
private abbrev cSpec11_1_15 := specAt11 1 15
private theorem cFlags11_1_15 : automaticFlags (trunkCatalog.states 11).context cSpec11_1_15 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_40 coordinateInput11_41 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_40 hCoordinate11_41]
  decide +kernel
private abbrev cSpec11_1_16 := specAt11 1 16
private theorem cFlags11_1_16 : automaticFlags (trunkCatalog.states 11).context cSpec11_1_16 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_16

private abbrev cSpec11_1_17 := specAt11 1 17
private theorem cFlags11_1_17 : automaticFlags (trunkCatalog.states 11).context cSpec11_1_17 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec11_0_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_17

private abbrev cSpec11_1_18 := specAt11 1 18
private theorem cFlags11_1_18 : automaticFlags (trunkCatalog.states 11).context cSpec11_1_18 = (List.replicate 5 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_0 coordinateInput11_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_0 hCoordinate11_33]
  decide +kernel
private abbrev cSpec11_1_19 := specAt11 1 19
private theorem cFlags11_1_19 : automaticFlags (trunkCatalog.states 11).context cSpec11_1_19 = (List.replicate 8 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_32 coordinateInput11_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_32 hCoordinate11_3]
  decide +kernel
private abbrev cSpec11_1_20 := specAt11 1 20
private theorem cFlags11_1_20 : automaticFlags (trunkCatalog.states 11).context cSpec11_1_20 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_20

private abbrev cSpec11_1_21 := specAt11 1 21
private theorem cFlags11_1_21 : automaticFlags (trunkCatalog.states 11).context cSpec11_1_21 = (List.replicate 1 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_31 coordinateInput11_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_31 hCoordinate11_33]
  decide +kernel
private abbrev cSpec11_2_1 := specAt11 2 1
private theorem cFlags11_2_1 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_1 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_1

private abbrev cSpec11_2_2 := specAt11 2 2
private theorem cFlags11_2_2 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_2 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec11_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_2

private abbrev cSpec11_2_3 := specAt11 2 3
private theorem cFlags11_2_3 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_3 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_3

private abbrev cSpec11_2_4 := specAt11 2 4
private theorem cFlags11_2_4 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_4 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_4

private abbrev cSpec11_2_5 := specAt11 2 5
private theorem cFlags11_2_5 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_5 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec11_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_5

private abbrev cSpec11_2_6 := specAt11 2 6
private theorem cFlags11_2_6 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_6 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_6

private abbrev cSpec11_2_7 := specAt11 2 7
private theorem cFlags11_2_7 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_7 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec11_0_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_7

private abbrev cSpec11_2_8 := specAt11 2 8
private theorem cFlags11_2_8 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_8 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_8

private abbrev cSpec11_2_9 := specAt11 2 9
private theorem cFlags11_2_9 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_9 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_9

private abbrev cSpec11_2_10 := specAt11 2 10
private theorem cFlags11_2_10 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_10 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec11_0_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_10

private abbrev cSpec11_2_11 := specAt11 2 11
private theorem cFlags11_2_11 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_11 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_42 coordinateInput11_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_42 hCoordinate11_43]
  decide +kernel
private abbrev cSpec11_2_12 := specAt11 2 12
private theorem cFlags11_2_12 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_12 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_44 coordinateInput11_45 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_44 hCoordinate11_45]
  decide +kernel
private abbrev cSpec11_2_13 := specAt11 2 13
private theorem cFlags11_2_13 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_13 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_46 coordinateInput11_47 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_46 hCoordinate11_47]
  decide +kernel
private abbrev cSpec11_2_14 := specAt11 2 14
private theorem cFlags11_2_14 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_14 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_48 coordinateInput11_49 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_48 hCoordinate11_49]
  decide +kernel
private abbrev cSpec11_2_15 := specAt11 2 15
private theorem cFlags11_2_15 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_15 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_50 coordinateInput11_51 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_50 hCoordinate11_51]
  decide +kernel
private abbrev cSpec11_2_16 := specAt11 2 16
private theorem cFlags11_2_16 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_16 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec11_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_1_11

private abbrev cSpec11_2_17 := specAt11 2 17
private theorem cFlags11_2_17 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec11_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_1_12

private abbrev cSpec11_2_18 := specAt11 2 18
private theorem cFlags11_2_18 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_18 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec11_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_1_13

private abbrev cSpec11_2_19 := specAt11 2 19
private theorem cFlags11_2_19 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_19 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec11_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_1_14

private abbrev cSpec11_2_20 := specAt11 2 20
private theorem cFlags11_2_20 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_20 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec11_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_1_15

private abbrev cSpec11_2_21 := specAt11 2 21
private theorem cFlags11_2_21 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_21 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_16

private abbrev cSpec11_2_22 := specAt11 2 22
private theorem cFlags11_2_22 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_22 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec11_0_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_17

private abbrev cSpec11_2_23 := specAt11 2 23
private theorem cFlags11_2_23 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_23 = (List.replicate 20 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_0 coordinateInput11_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_0 hCoordinate11_43]
  decide +kernel
private abbrev cSpec11_2_24 := specAt11 2 24
private theorem cFlags11_2_24 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_24 = (List.replicate 8 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_42 coordinateInput11_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_42 hCoordinate11_3]
  decide +kernel
private abbrev cSpec11_2_25 := specAt11 2 25
private theorem cFlags11_2_25 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_25 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_20

private abbrev cSpec11_2_26 := specAt11 2 26
private theorem cFlags11_2_26 : automaticFlags (trunkCatalog.states 11).context cSpec11_2_26 = (List.replicate 1 true) := by
  exact (automaticFlags_same _ _ cSpec11_1_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_1_21

private abbrev cSpec11_3_1 := specAt11 3 1
private theorem cFlags11_3_1 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_1 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_1

private abbrev cSpec11_3_2 := specAt11 3 2
private theorem cFlags11_3_2 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_2 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec11_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_2

private abbrev cSpec11_3_3 := specAt11 3 3
private theorem cFlags11_3_3 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_3 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_3

private abbrev cSpec11_3_4 := specAt11 3 4
private theorem cFlags11_3_4 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_4 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_4

private abbrev cSpec11_3_5 := specAt11 3 5
private theorem cFlags11_3_5 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_5 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec11_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_5

private abbrev cSpec11_3_6 := specAt11 3 6
private theorem cFlags11_3_6 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_6 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_52 coordinateInput11_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_52 hCoordinate11_53]
  decide +kernel
private abbrev cSpec11_3_7 := specAt11 3 7
private theorem cFlags11_3_7 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_7 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_54 coordinateInput11_55 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_54 hCoordinate11_55]
  decide +kernel
private abbrev cSpec11_3_8 := specAt11 3 8
private theorem cFlags11_3_8 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_8 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_56 coordinateInput11_57 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_56 hCoordinate11_57]
  decide +kernel
private abbrev cSpec11_3_9 := specAt11 3 9
private theorem cFlags11_3_9 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_9 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_58 coordinateInput11_59 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_58 hCoordinate11_59]
  decide +kernel
private abbrev cSpec11_3_10 := specAt11 3 10
private theorem cFlags11_3_10 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_10 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_60 coordinateInput11_61 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_60 hCoordinate11_61]
  decide +kernel
private abbrev cSpec11_3_11 := specAt11 3 11
private theorem cFlags11_3_11 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_11 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_62 coordinateInput11_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_62 hCoordinate11_63]
  decide +kernel
private abbrev cSpec11_3_12 := specAt11 3 12
private theorem cFlags11_3_12 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_12 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_64 coordinateInput11_65 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_64 hCoordinate11_65]
  decide +kernel
private abbrev cSpec11_3_13 := specAt11 3 13
private theorem cFlags11_3_13 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_13 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_66 coordinateInput11_67 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_66 hCoordinate11_67]
  decide +kernel
private abbrev cSpec11_3_14 := specAt11 3 14
private theorem cFlags11_3_14 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_14 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_68 coordinateInput11_69 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_68 hCoordinate11_69]
  decide +kernel
private abbrev cSpec11_3_15 := specAt11 3 15
private theorem cFlags11_3_15 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_15 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_70 coordinateInput11_71 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_70 hCoordinate11_71]
  decide +kernel
private abbrev cSpec11_3_16 := specAt11 3 16
private theorem cFlags11_3_16 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_16 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec11_2_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_2_11

private abbrev cSpec11_3_17 := specAt11 3 17
private theorem cFlags11_3_17 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec11_2_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_2_12

private abbrev cSpec11_3_18 := specAt11 3 18
private theorem cFlags11_3_18 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_18 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec11_2_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_2_13

private abbrev cSpec11_3_19 := specAt11 3 19
private theorem cFlags11_3_19 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_19 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec11_2_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_2_14

private abbrev cSpec11_3_20 := specAt11 3 20
private theorem cFlags11_3_20 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_20 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec11_2_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_2_15

private abbrev cSpec11_3_21 := specAt11 3 21
private theorem cFlags11_3_21 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_21 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_72 coordinateInput11_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_72 hCoordinate11_73]
  decide +kernel
private abbrev cSpec11_3_22 := specAt11 3 22
private theorem cFlags11_3_22 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_22 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_74 coordinateInput11_75 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_74 hCoordinate11_75]
  decide +kernel
private abbrev cSpec11_3_23 := specAt11 3 23
private theorem cFlags11_3_23 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_23 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_76 coordinateInput11_77 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_76 hCoordinate11_77]
  decide +kernel
private abbrev cSpec11_3_24 := specAt11 3 24
private theorem cFlags11_3_24 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_24 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_78 coordinateInput11_79 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_78 hCoordinate11_79]
  decide +kernel
private abbrev cSpec11_3_25 := specAt11 3 25
private theorem cFlags11_3_25 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_25 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_80 coordinateInput11_81 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_80 hCoordinate11_81]
  decide +kernel
private abbrev cSpec11_3_26 := specAt11 3 26
private theorem cFlags11_3_26 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec11_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_1_11

private abbrev cSpec11_3_27 := specAt11 3 27
private theorem cFlags11_3_27 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec11_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_1_12

private abbrev cSpec11_3_28 := specAt11 3 28
private theorem cFlags11_3_28 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec11_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_1_13

private abbrev cSpec11_3_29 := specAt11 3 29
private theorem cFlags11_3_29 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec11_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_1_14

private abbrev cSpec11_3_30 := specAt11 3 30
private theorem cFlags11_3_30 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec11_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_1_15

private abbrev cSpec11_3_31 := specAt11 3 31
private theorem cFlags11_3_31 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_31 = (List.replicate 8 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_2 coordinateInput11_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_2 hCoordinate11_53]
  decide +kernel
private abbrev cSpec11_3_32 := specAt11 3 32
private theorem cFlags11_3_32 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_32 = (List.replicate 8 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_52 coordinateInput11_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_52 hCoordinate11_1]
  decide +kernel
private abbrev cSpec11_3_33 := specAt11 3 33
private theorem cFlags11_3_33 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_33 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_52 coordinateInput11_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_52 hCoordinate11_63]
  decide +kernel
private abbrev cSpec11_3_34 := specAt11 3 34
private theorem cFlags11_3_34 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_34 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_62 coordinateInput11_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_62 hCoordinate11_53]
  decide +kernel
private abbrev cSpec11_3_35 := specAt11 3 35
private theorem cFlags11_3_35 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_35 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_62 coordinateInput11_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_62 hCoordinate11_43]
  decide +kernel
private abbrev cSpec11_3_36 := specAt11 3 36
private theorem cFlags11_3_36 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_36 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_42 coordinateInput11_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_42 hCoordinate11_63]
  decide +kernel
private abbrev cSpec11_3_37 := specAt11 3 37
private theorem cFlags11_3_37 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_37 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_42 coordinateInput11_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_42 hCoordinate11_73]
  decide +kernel
private abbrev cSpec11_3_38 := specAt11 3 38
private theorem cFlags11_3_38 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_38 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_72 coordinateInput11_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_72 hCoordinate11_43]
  decide +kernel
private abbrev cSpec11_3_39 := specAt11 3 39
private theorem cFlags11_3_39 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_39 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_72 coordinateInput11_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_72 hCoordinate11_33]
  decide +kernel
private abbrev cSpec11_3_40 := specAt11 3 40
private theorem cFlags11_3_40 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_40 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_32 coordinateInput11_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_32 hCoordinate11_73]
  decide +kernel
private abbrev cSpec11_3_41 := specAt11 3 41
private theorem cFlags11_3_41 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_41 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_20

private abbrev cSpec11_3_42 := specAt11 3 42
private theorem cFlags11_3_42 : automaticFlags (trunkCatalog.states 11).context cSpec11_3_42 = (List.replicate 1 true) := by
  exact (automaticFlags_same _ _ cSpec11_1_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_1_21

private abbrev cSpec11_4_1 := specAt11 4 1
private theorem cFlags11_4_1 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_1 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_1

private abbrev cSpec11_4_2 := specAt11 4 2
private theorem cFlags11_4_2 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_2 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec11_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_2

private abbrev cSpec11_4_3 := specAt11 4 3
private theorem cFlags11_4_3 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_3 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_3

private abbrev cSpec11_4_4 := specAt11 4 4
private theorem cFlags11_4_4 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_4 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_4

private abbrev cSpec11_4_5 := specAt11 4 5
private theorem cFlags11_4_5 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_5 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec11_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_5

private abbrev cSpec11_4_6 := specAt11 4 6
private theorem cFlags11_4_6 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_6 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec11_3_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_3_6

private abbrev cSpec11_4_7 := specAt11 4 7
private theorem cFlags11_4_7 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_7 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec11_3_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_3_7

private abbrev cSpec11_4_8 := specAt11 4 8
private theorem cFlags11_4_8 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_8 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec11_3_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_3_8

private abbrev cSpec11_4_9 := specAt11 4 9
private theorem cFlags11_4_9 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_9 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec11_3_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_3_9

private abbrev cSpec11_4_10 := specAt11 4 10
private theorem cFlags11_4_10 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_10 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec11_3_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_3_10

private abbrev cSpec11_4_11 := specAt11 4 11
private theorem cFlags11_4_11 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_11 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_82 coordinateInput11_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_82 hCoordinate11_83]
  decide +kernel
private abbrev cSpec11_4_12 := specAt11 4 12
private theorem cFlags11_4_12 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_12 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_84 coordinateInput11_85 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_84 hCoordinate11_85]
  decide +kernel
private abbrev cSpec11_4_13 := specAt11 4 13
private theorem cFlags11_4_13 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_13 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_86 coordinateInput11_87 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_86 hCoordinate11_87]
  decide +kernel
private abbrev cSpec11_4_14 := specAt11 4 14
private theorem cFlags11_4_14 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_14 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_88 coordinateInput11_89 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_88 hCoordinate11_89]
  decide +kernel
private abbrev cSpec11_4_15 := specAt11 4 15
private theorem cFlags11_4_15 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_15 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_90 coordinateInput11_91 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_90 hCoordinate11_91]
  decide +kernel
private abbrev cSpec11_4_16 := specAt11 4 16
private theorem cFlags11_4_16 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_16 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec11_2_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_2_11

private abbrev cSpec11_4_17 := specAt11 4 17
private theorem cFlags11_4_17 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec11_2_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_2_12

private abbrev cSpec11_4_18 := specAt11 4 18
private theorem cFlags11_4_18 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_18 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec11_2_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_2_13

private abbrev cSpec11_4_19 := specAt11 4 19
private theorem cFlags11_4_19 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_19 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec11_2_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_2_14

private abbrev cSpec11_4_20 := specAt11 4 20
private theorem cFlags11_4_20 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_20 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec11_2_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_2_15

private abbrev cSpec11_4_21 := specAt11 4 21
private theorem cFlags11_4_21 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_21 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec11_3_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_3_21

private abbrev cSpec11_4_22 := specAt11 4 22
private theorem cFlags11_4_22 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_22 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec11_3_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_3_22

private abbrev cSpec11_4_23 := specAt11 4 23
private theorem cFlags11_4_23 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_23 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec11_3_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_3_23

private abbrev cSpec11_4_24 := specAt11 4 24
private theorem cFlags11_4_24 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_24 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec11_3_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_3_24

private abbrev cSpec11_4_25 := specAt11 4 25
private theorem cFlags11_4_25 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_25 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec11_3_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_3_25

private abbrev cSpec11_4_26 := specAt11 4 26
private theorem cFlags11_4_26 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec11_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_1_11

private abbrev cSpec11_4_27 := specAt11 4 27
private theorem cFlags11_4_27 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec11_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_1_12

private abbrev cSpec11_4_28 := specAt11 4 28
private theorem cFlags11_4_28 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec11_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_1_13

private abbrev cSpec11_4_29 := specAt11 4 29
private theorem cFlags11_4_29 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec11_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_1_14

private abbrev cSpec11_4_30 := specAt11 4 30
private theorem cFlags11_4_30 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec11_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_1_15

private abbrev cSpec11_4_31 := specAt11 4 31
private theorem cFlags11_4_31 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_31 = (List.replicate 8 true) := by
  exact (automaticFlags_same _ _ cSpec11_3_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_3_31

private abbrev cSpec11_4_32 := specAt11 4 32
private theorem cFlags11_4_32 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_32 = (List.replicate 8 false) := by
  exact (automaticFlags_same _ _ cSpec11_3_32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_3_32

private abbrev cSpec11_4_33 := specAt11 4 33
private theorem cFlags11_4_33 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_33 = (List.replicate 8 true) := by
  rw [automaticFlags_cached _ _ coordinateInput11_52 coordinateInput11_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_52 hCoordinate11_83]
  decide +kernel
private abbrev cSpec11_4_34 := specAt11 4 34
private theorem cFlags11_4_34 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_34 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_82 coordinateInput11_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_82 hCoordinate11_53]
  decide +kernel
private abbrev cSpec11_4_35 := specAt11 4 35
private theorem cFlags11_4_35 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_35 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_82 coordinateInput11_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_82 hCoordinate11_43]
  decide +kernel
private abbrev cSpec11_4_36 := specAt11 4 36
private theorem cFlags11_4_36 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_36 = (List.replicate 8 false) := by
  rw [automaticFlags_cached _ _ coordinateInput11_42 coordinateInput11_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate11_42 hCoordinate11_83]
  decide +kernel
private abbrev cSpec11_4_37 := specAt11 4 37
private theorem cFlags11_4_37 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_37 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec11_3_37 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_3_37

private abbrev cSpec11_4_38 := specAt11 4 38
private theorem cFlags11_4_38 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_38 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec11_3_38 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_3_38

private abbrev cSpec11_4_39 := specAt11 4 39
private theorem cFlags11_4_39 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_39 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec11_3_39 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_3_39

private abbrev cSpec11_4_40 := specAt11 4 40
private theorem cFlags11_4_40 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_40 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec11_3_40 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_3_40

private abbrev cSpec11_4_41 := specAt11 4 41
private theorem cFlags11_4_41 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_41 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec11_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_0_20

private abbrev cSpec11_4_42 := specAt11 4 42
private theorem cFlags11_4_42 : automaticFlags (trunkCatalog.states 11).context cSpec11_4_42 = (List.replicate 1 true) := by
  exact (automaticFlags_same _ _ cSpec11_1_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags11_1_21

private theorem keys_eq : coverageKeys (trunkCatalog.states 11) = checkedKeys := by
  rfl
private theorem tasks_eq : coverageTasks (trunkCatalog.states 11) = checkedTasks := by
  rw [← coverageTasksProjection_eq]
  change [(0,[(1, (automaticFlags (trunkCatalog.states 11).context cSpec11_0_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 11).context cSpec11_0_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 11).context cSpec11_0_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 11).context cSpec11_0_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 11).context cSpec11_0_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 11).context cSpec11_0_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 11).context cSpec11_0_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 11).context cSpec11_0_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 11).context cSpec11_0_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 11).context cSpec11_0_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 11).context cSpec11_0_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 11).context cSpec11_0_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 11).context cSpec11_0_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 11).context cSpec11_0_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 11).context cSpec11_0_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 11).context cSpec11_0_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 11).context cSpec11_0_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 11).context cSpec11_0_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 11).context cSpec11_0_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 11).context cSpec11_0_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 11).context cSpec11_0_21).zipIdx.map Prod.swap)]),(1,[(1, (automaticFlags (trunkCatalog.states 11).context cSpec11_1_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 11).context cSpec11_1_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 11).context cSpec11_1_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 11).context cSpec11_1_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 11).context cSpec11_1_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 11).context cSpec11_1_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 11).context cSpec11_1_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 11).context cSpec11_1_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 11).context cSpec11_1_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 11).context cSpec11_1_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 11).context cSpec11_1_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 11).context cSpec11_1_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 11).context cSpec11_1_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 11).context cSpec11_1_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 11).context cSpec11_1_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 11).context cSpec11_1_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 11).context cSpec11_1_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 11).context cSpec11_1_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 11).context cSpec11_1_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 11).context cSpec11_1_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 11).context cSpec11_1_21).zipIdx.map Prod.swap)]),(2,[(1, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 11).context cSpec11_2_26).zipIdx.map Prod.swap)]),(3,[(1, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 11).context cSpec11_3_42).zipIdx.map Prod.swap)]),(4,[(1, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 11).context cSpec11_4_42).zipIdx.map Prod.swap)])] = checkedTasks
  rw [cFlags11_0_1, cFlags11_0_2, cFlags11_0_3, cFlags11_0_4, cFlags11_0_5, cFlags11_0_6, cFlags11_0_7, cFlags11_0_8, cFlags11_0_9, cFlags11_0_10, cFlags11_0_11, cFlags11_0_12, cFlags11_0_13, cFlags11_0_14, cFlags11_0_15, cFlags11_0_16, cFlags11_0_17, cFlags11_0_18, cFlags11_0_19, cFlags11_0_20, cFlags11_0_21, cFlags11_1_1, cFlags11_1_2, cFlags11_1_3, cFlags11_1_4, cFlags11_1_5, cFlags11_1_6, cFlags11_1_7, cFlags11_1_8, cFlags11_1_9, cFlags11_1_10, cFlags11_1_11, cFlags11_1_12, cFlags11_1_13, cFlags11_1_14, cFlags11_1_15, cFlags11_1_16, cFlags11_1_17, cFlags11_1_18, cFlags11_1_19, cFlags11_1_20, cFlags11_1_21, cFlags11_2_1, cFlags11_2_2, cFlags11_2_3, cFlags11_2_4, cFlags11_2_5, cFlags11_2_6, cFlags11_2_7, cFlags11_2_8, cFlags11_2_9, cFlags11_2_10, cFlags11_2_11, cFlags11_2_12, cFlags11_2_13, cFlags11_2_14, cFlags11_2_15, cFlags11_2_16, cFlags11_2_17, cFlags11_2_18, cFlags11_2_19, cFlags11_2_20, cFlags11_2_21, cFlags11_2_22, cFlags11_2_23, cFlags11_2_24, cFlags11_2_25, cFlags11_2_26, cFlags11_3_1, cFlags11_3_2, cFlags11_3_3, cFlags11_3_4, cFlags11_3_5, cFlags11_3_6, cFlags11_3_7, cFlags11_3_8, cFlags11_3_9, cFlags11_3_10, cFlags11_3_11, cFlags11_3_12, cFlags11_3_13, cFlags11_3_14, cFlags11_3_15, cFlags11_3_16, cFlags11_3_17, cFlags11_3_18, cFlags11_3_19, cFlags11_3_20, cFlags11_3_21, cFlags11_3_22, cFlags11_3_23, cFlags11_3_24, cFlags11_3_25, cFlags11_3_26, cFlags11_3_27, cFlags11_3_28, cFlags11_3_29, cFlags11_3_30, cFlags11_3_31, cFlags11_3_32, cFlags11_3_33, cFlags11_3_34, cFlags11_3_35, cFlags11_3_36, cFlags11_3_37, cFlags11_3_38, cFlags11_3_39, cFlags11_3_40, cFlags11_3_41, cFlags11_3_42, cFlags11_4_1, cFlags11_4_2, cFlags11_4_3, cFlags11_4_4, cFlags11_4_5, cFlags11_4_6, cFlags11_4_7, cFlags11_4_8, cFlags11_4_9, cFlags11_4_10, cFlags11_4_11, cFlags11_4_12, cFlags11_4_13, cFlags11_4_14, cFlags11_4_15, cFlags11_4_16, cFlags11_4_17, cFlags11_4_18, cFlags11_4_19, cFlags11_4_20, cFlags11_4_21, cFlags11_4_22, cFlags11_4_23, cFlags11_4_24, cFlags11_4_25, cFlags11_4_26, cFlags11_4_27, cFlags11_4_28, cFlags11_4_29, cFlags11_4_30, cFlags11_4_31, cFlags11_4_32, cFlags11_4_33, cFlags11_4_34, cFlags11_4_35, cFlags11_4_36, cFlags11_4_37, cFlags11_4_38, cFlags11_4_39, cFlags11_4_40, cFlags11_4_41, cFlags11_4_42]
  rfl
private def decodeThresholdBound (b : ℕ × Bool × Bool) : CertBound :=
  ⟨b.2.1,b.2.2,(Freiman.TrunkFast.fastBound b.1).threshold⟩
private def decodeGoalBranch (a : List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) : List CertBound × LowerHistoryComparison :=
  (a.1.map decodeThresholdBound, match a.2 with
    | none => .impossible
    | some none => .automatic
    | some (some b) => .bound (decodeThresholdBound b))
private def thresholdParentA11 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(3, false, false), (10, false, false)], some (some (23, true, false))),
 ([(3, false, false), (10, true, true)], some (some (23, true, false))),
 ([(3, true, true), (30, false, false), (29, false, true), (10, false, false)], some (some (23, true, false))),
 ([(3, true, true), (30, false, false), (29, false, true), (10, true, true)], some (some (23, true, false))),
 ([(3, true, true), (30, false, false), (29, true, false), (10, false, false)], some (some (145, true, false))),
 ([(3, true, true), (30, false, false), (29, true, false), (10, true, true)], some (some (145, true, false))),
 ([(3, true, true), (30, true, true), (147, true, true), (10, false, false)], some (some (23, true, false))),
 ([(3, true, true), (30, true, true), (147, true, true), (10, true, true)], some (some (23, true, false))),
 ([(3, true, true), (30, true, true), (147, false, false), (10, false, false)], some (some (150, true, false))),
 ([(3, true, true), (30, true, true), (147, false, false), (10, true, true)], some (some (150, true, false)))]
private def thresholdParentB11 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(10, false, false), (3, false, false)], some none),
 ([(10, false, false), (3, true, true)], some none),
 ([(10, true, true), (3, false, false)], some none),
 ([(10, true, true), (3, true, true)], some none)]

private theorem hThresholdParentA11 : trunkBranches (trunkCatalog.states 11).context ⟨([2],[]),true,([1],[]),false,false,[]⟩ = thresholdParentA11.map decodeGoalBranch := by decide +kernel
private theorem hThresholdParentB11 : trunkBranches (trunkCatalog.states 11).context ⟨([1],[]),true,([2],[]),false,false,[]⟩ = thresholdParentB11.map decodeGoalBranch := by decide +kernel
private theorem hActualParentLength11 : (trunkParents (trunkCatalog.states 11).context).length = 30 := by
  unfold trunkParents
  rw [hThresholdParentA11,hThresholdParentB11]
  decide +kernel

private theorem parents_length : (trunkParents (trunkCatalog.states 11).context).length = 30 := hActualParentLength11
private theorem table_checked : coverageTable checkedKeys checkedTasks 30 := by
  apply coverageRemainder_sound _ _ _ [[7, 13], [], [13, 17, 23, 29], [23], [23]]
  unfold coverageRemainder parentsFor
  decide +kernel

theorem solution : trunkCoverage trunkCatalog 11 := by
  apply coverageTable_sound 11
  · unfold certRectangleValid; decide +kernel
  · decide +kernel
  · rw [keys_eq, tasks_eq, parents_length]
    exact table_checked
#print axioms solution
