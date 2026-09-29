-- Prove2me | solution 1 for Freiman.trunk_coverage_03
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:44:38.049274+00:00
-- url     : https://prove2.me/submissions/15882a3d-ba97-4633-90db-8348790bac36

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

private def coordinateFields3 : Array CertField := #[⟨(4/13),(1/13),(0/1),(0/1)⟩,⟨(1/2),(1/6),(0/1),(0/1)⟩,⟨(52/73),(1/73),(0/1),(0/1)⟩,⟨(89/214),(1/214),(0/1),(0/1)⟩,⟨(9/13),(-1/13),(0/1),(0/1)⟩,⟨(15/37),(-1/37),(0/1),(0/1)⟩,⟨(22/37),(1/37),(0/1),(0/1)⟩,⟨(113/179),(1/537),(0/1),(0/1)⟩,⟨(17/22),(-1/22),(0/1),(0/1)⟩,⟨(735/1006),(1/1006),(0/1),(0/1)⟩,⟨(66/179),(-1/537),(0/1),(0/1)⟩,⟨(125/214),(-1/214),(0/1),(0/1)⟩,⟨(35/94),(1/94),(0/1),(0/1)⟩,⟨(553/1429),(1/1429),(0/1),(0/1)⟩,⟨(10/23),(-1/69),(0/1),(0/1)⟩,⟨(1272/3013),(1/3013),(0/1),(0/1)⟩,⟨(5/22),(1/22),(0/1),(0/1)⟩,⟨(42/143),(1/429),(0/1),(0/1)⟩,⟨(271/1006),(-1/1006),(0/1),(0/1)⟩,⟨(16/59),(1/177),(0/1),(0/1)⟩,⟨(767/2749),(1/2749),(0/1),(0/1)⟩,⟨(43/142),(-1/142),(0/1),(0/1)⟩,⟨(1809/6094),(1/6094),(0/1),(0/1)⟩,⟨(2/1),(-1/1),(0/1),(0/1)⟩,⟨(731/2497),(-1/2497),(0/1),(0/1)⟩,⟨(517/1249),(-1/1249),(0/1),(0/1)⟩,⟨(101/143),(-1/429),(0/1),(0/1)⟩,⟨(13/23),(1/69),(0/1),(0/1)⟩,⟨(732/1249),(1/1249),(0/1),(0/1)⟩,⟨(59/94),(-1/94),(0/1),(0/1)⟩]
private abbrev coordinateInput3_0 : LowerPair × Bool × Bool := (([2], []), true, false)
private def coordinateCodes3_0 : List (ℕ × ℕ) := [(0, 1), (0, 1), (0, 2), (0, 1), (3, 1)]
private abbrev coordinateInput3_1 : LowerPair × Bool × Bool := (([1], []), false, false)
private def coordinateCodes3_1 : List (ℕ × ℕ) := [(4, 5), (4, 5)]
private abbrev coordinateInput3_2 : LowerPair × Bool × Bool := (([1], []), true, false)
private def coordinateCodes3_2 : List (ℕ × ℕ) := [(1, 1), (1, 1), (1, 2), (1, 1), (2, 1)]
private abbrev coordinateInput3_3 : LowerPair × Bool × Bool := (([2], []), false, false)
private def coordinateCodes3_3 : List (ℕ × ℕ) := [(5, 5), (5, 5)]
private abbrev coordinateInput3_4 : LowerPair × Bool × Bool := (([1, 1], []), true, false)
private def coordinateCodes3_4 : List (ℕ × ℕ) := [(6, 1), (6, 2), (6, 1), (7, 1)]
private abbrev coordinateInput3_5 : LowerPair × Bool × Bool := (([1, 2], []), false, false)
private def coordinateCodes3_5 : List (ℕ × ℕ) := [(8, 5)]
private abbrev coordinateInput3_6 : LowerPair × Bool × Bool := (([1, 2], []), true, false)
private def coordinateCodes3_6 : List (ℕ × ℕ) := [(2, 1), (2, 2), (2, 1), (9, 1)]
private abbrev coordinateInput3_7 : LowerPair × Bool × Bool := (([1, 1], []), false, false)
private def coordinateCodes3_7 : List (ℕ × ℕ) := [(4, 5)]
private abbrev coordinateInput3_8 : LowerPair × Bool × Bool := (([1], [1]), true, true)
private def coordinateCodes3_8 : List (ℕ × ℕ) := [(1, 1), (1, 2), (1, 1), (2, 1)]
private abbrev coordinateInput3_9 : LowerPair × Bool × Bool := (([1], [2]), false, true)
private def coordinateCodes3_9 : List (ℕ × ℕ) := [(4, 5), (4, 10), (4, 5), (11, 5)]
private abbrev coordinateInput3_10 : LowerPair × Bool × Bool := (([1], [2]), true, true)
private def coordinateCodes3_10 : List (ℕ × ℕ) := [(1, 0), (1, 3), (1, 0), (2, 0)]
private abbrev coordinateInput3_11 : LowerPair × Bool × Bool := (([1], [1]), false, true)
private def coordinateCodes3_11 : List (ℕ × ℕ) := [(4, 4), (4, 11), (4, 4), (11, 4)]
private abbrev coordinateInput3_12 : LowerPair × Bool × Bool := (([2, 1], []), true, false)
private def coordinateCodes3_12 : List (ℕ × ℕ) := [(12, 1), (12, 2), (12, 1), (13, 1)]
private abbrev coordinateInput3_13 : LowerPair × Bool × Bool := (([2, 2], []), false, false)
private def coordinateCodes3_13 : List (ℕ × ℕ) := [(14, 5)]
private abbrev coordinateInput3_14 : LowerPair × Bool × Bool := (([2, 2], []), true, false)
private def coordinateCodes3_14 : List (ℕ × ℕ) := [(3, 1), (3, 2), (3, 1), (15, 1)]
private abbrev coordinateInput3_15 : LowerPair × Bool × Bool := (([2, 1], []), false, false)
private def coordinateCodes3_15 : List (ℕ × ℕ) := [(5, 5)]
private abbrev coordinateInput3_16 : LowerPair × Bool × Bool := (([2], [1]), true, true)
private def coordinateCodes3_16 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 1), (3, 1)]
private abbrev coordinateInput3_17 : LowerPair × Bool × Bool := (([2], [2]), false, true)
private def coordinateCodes3_17 : List (ℕ × ℕ) := [(5, 5), (5, 10), (5, 5), (10, 5)]
private abbrev coordinateInput3_18 : LowerPair × Bool × Bool := (([2], [2]), true, true)
private def coordinateCodes3_18 : List (ℕ × ℕ) := [(0, 0), (0, 3), (0, 0), (3, 0)]
private abbrev coordinateInput3_19 : LowerPair × Bool × Bool := (([2], [1]), false, true)
private def coordinateCodes3_19 : List (ℕ × ℕ) := [(5, 4), (5, 11), (5, 4), (10, 4)]
private abbrev coordinateInput3_20 : LowerPair × Bool × Bool := (([3], []), true, false)
private def coordinateCodes3_20 : List (ℕ × ℕ) := [(16, 1), (16, 1), (16, 2), (16, 1), (17, 1)]
private abbrev coordinateInput3_21 : LowerPair × Bool × Bool := (([3], []), false, false)
private def coordinateCodes3_21 : List (ℕ × ℕ) := [(18, 5), (18, 5)]
private abbrev coordinateInput3_22 : LowerPair × Bool × Bool := (([3, 1], []), true, false)
private def coordinateCodes3_22 : List (ℕ × ℕ) := [(19, 1), (19, 2), (19, 1), (20, 1)]
private abbrev coordinateInput3_23 : LowerPair × Bool × Bool := (([3, 2], []), false, false)
private def coordinateCodes3_23 : List (ℕ × ℕ) := [(21, 5)]
private abbrev coordinateInput3_24 : LowerPair × Bool × Bool := (([3, 2], []), true, false)
private def coordinateCodes3_24 : List (ℕ × ℕ) := [(17, 1), (17, 2), (17, 1), (22, 1)]
private abbrev coordinateInput3_25 : LowerPair × Bool × Bool := (([3, 1], []), false, false)
private def coordinateCodes3_25 : List (ℕ × ℕ) := [(18, 5)]
private abbrev coordinateInput3_26 : LowerPair × Bool × Bool := (([3], [1]), true, true)
private def coordinateCodes3_26 : List (ℕ × ℕ) := [(16, 1), (16, 2), (16, 1), (17, 1)]
private abbrev coordinateInput3_27 : LowerPair × Bool × Bool := (([3], [2]), false, true)
private def coordinateCodes3_27 : List (ℕ × ℕ) := [(18, 5)]
private abbrev coordinateInput3_28 : LowerPair × Bool × Bool := (([3], [2]), true, true)
private def coordinateCodes3_28 : List (ℕ × ℕ) := [(16, 0), (16, 3), (16, 0), (17, 0)]
private abbrev coordinateInput3_29 : LowerPair × Bool × Bool := (([3], [1]), false, true)
private def coordinateCodes3_29 : List (ℕ × ℕ) := [(18, 4)]
private abbrev coordinateInput3_30 : LowerPair × Bool × Bool := (([], []), true, false)
private def coordinateCodes3_30 : List (ℕ × ℕ) := [(1, 1), (1, 2), (1, 1), (2, 1)]
private abbrev coordinateInput3_31 : LowerPair × Bool × Bool := (([], []), false, false)
private def coordinateCodes3_31 : List (ℕ × ℕ) := [(23, 5)]
private abbrev coordinateInput3_32 : LowerPair × Bool × Bool := (([3], [2]), true, false)
private def coordinateCodes3_32 : List (ℕ × ℕ) := [(16, 0), (16, 3), (16, 0), (17, 0)]
private abbrev coordinateInput3_33 : LowerPair × Bool × Bool := (([3], [2]), false, false)
private def coordinateCodes3_33 : List (ℕ × ℕ) := [(18, 5)]
private abbrev coordinateInput3_34 : LowerPair × Bool × Bool := (([3, 1], [2]), true, false)
private def coordinateCodes3_34 : List (ℕ × ℕ) := [(19, 0), (19, 3), (19, 0), (20, 0), (19, 0)]
private abbrev coordinateInput3_35 : LowerPair × Bool × Bool := (([3, 2], [2]), false, false)
private def coordinateCodes3_35 : List (ℕ × ℕ) := [(21, 5), (21, 5), (21, 10), (21, 5), (24, 5)]
private abbrev coordinateInput3_36 : LowerPair × Bool × Bool := (([3, 2], [2]), true, false)
private def coordinateCodes3_36 : List (ℕ × ℕ) := [(17, 0), (17, 3), (17, 0), (22, 0), (17, 0)]
private abbrev coordinateInput3_37 : LowerPair × Bool × Bool := (([3, 1], [2]), false, false)
private def coordinateCodes3_37 : List (ℕ × ℕ) := [(18, 5), (18, 5)]
private abbrev coordinateInput3_38 : LowerPair × Bool × Bool := (([3], [2, 1]), true, true)
private def coordinateCodes3_38 : List (ℕ × ℕ) := [(16, 12), (16, 12), (16, 13), (16, 12), (17, 12)]
private abbrev coordinateInput3_39 : LowerPair × Bool × Bool := (([3], [2, 2]), false, true)
private def coordinateCodes3_39 : List (ℕ × ℕ) := [(18, 14), (18, 14)]
private abbrev coordinateInput3_40 : LowerPair × Bool × Bool := (([3], [2, 2]), true, true)
private def coordinateCodes3_40 : List (ℕ × ℕ) := [(16, 3), (16, 3), (16, 15), (16, 3), (17, 3)]
private abbrev coordinateInput3_41 : LowerPair × Bool × Bool := (([3], [2, 1]), false, true)
private def coordinateCodes3_41 : List (ℕ × ℕ) := [(18, 5), (18, 5)]
private abbrev coordinateInput3_42 : LowerPair × Bool × Bool := (([2], [2]), true, false)
private def coordinateCodes3_42 : List (ℕ × ℕ) := [(0, 0), (0, 3), (0, 0), (3, 0)]
private abbrev coordinateInput3_43 : LowerPair × Bool × Bool := (([2], [2]), false, false)
private def coordinateCodes3_43 : List (ℕ × ℕ) := [(5, 5), (5, 10), (5, 5), (10, 5)]
private abbrev coordinateInput3_44 : LowerPair × Bool × Bool := (([2, 1], [2]), true, false)
private def coordinateCodes3_44 : List (ℕ × ℕ) := [(12, 0), (12, 3), (12, 0), (13, 0), (12, 0)]
private abbrev coordinateInput3_45 : LowerPair × Bool × Bool := (([2, 2], [2]), false, false)
private def coordinateCodes3_45 : List (ℕ × ℕ) := [(14, 5), (14, 5), (14, 10), (14, 5), (25, 5)]
private abbrev coordinateInput3_46 : LowerPair × Bool × Bool := (([2, 2], [2]), true, false)
private def coordinateCodes3_46 : List (ℕ × ℕ) := [(3, 0), (3, 3), (3, 0), (15, 0), (3, 0)]
private abbrev coordinateInput3_47 : LowerPair × Bool × Bool := (([2, 1], [2]), false, false)
private def coordinateCodes3_47 : List (ℕ × ℕ) := [(5, 5), (5, 5), (5, 10), (5, 5), (10, 5)]
private abbrev coordinateInput3_48 : LowerPair × Bool × Bool := (([2], [2, 1]), true, true)
private def coordinateCodes3_48 : List (ℕ × ℕ) := [(0, 12), (0, 12), (0, 13), (0, 12), (3, 12)]
private abbrev coordinateInput3_49 : LowerPair × Bool × Bool := (([2], [2, 2]), false, true)
private def coordinateCodes3_49 : List (ℕ × ℕ) := [(5, 14), (5, 25), (5, 14), (10, 14), (5, 14)]
private abbrev coordinateInput3_50 : LowerPair × Bool × Bool := (([2], [2, 2]), true, true)
private def coordinateCodes3_50 : List (ℕ × ℕ) := [(0, 3), (0, 3), (0, 15), (0, 3), (3, 3)]
private abbrev coordinateInput3_51 : LowerPair × Bool × Bool := (([2], [2, 1]), false, true)
private def coordinateCodes3_51 : List (ℕ × ℕ) := [(5, 5), (5, 10), (5, 5), (10, 5), (5, 5)]
private abbrev coordinateInput3_52 : LowerPair × Bool × Bool := (([2], [1]), true, false)
private def coordinateCodes3_52 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 1), (3, 1)]
private abbrev coordinateInput3_53 : LowerPair × Bool × Bool := (([2], [1]), false, false)
private def coordinateCodes3_53 : List (ℕ × ℕ) := [(5, 4), (5, 11), (5, 4), (10, 4)]
private abbrev coordinateInput3_54 : LowerPair × Bool × Bool := (([2, 1], [1]), true, false)
private def coordinateCodes3_54 : List (ℕ × ℕ) := [(12, 1), (12, 2), (12, 1), (13, 1), (12, 1)]
private abbrev coordinateInput3_55 : LowerPair × Bool × Bool := (([2, 2], [1]), false, false)
private def coordinateCodes3_55 : List (ℕ × ℕ) := [(14, 4), (14, 4), (14, 11), (14, 4), (25, 4)]
private abbrev coordinateInput3_56 : LowerPair × Bool × Bool := (([2, 2], [1]), true, false)
private def coordinateCodes3_56 : List (ℕ × ℕ) := [(3, 1), (3, 2), (3, 1), (15, 1), (3, 1)]
private abbrev coordinateInput3_57 : LowerPair × Bool × Bool := (([2, 1], [1]), false, false)
private def coordinateCodes3_57 : List (ℕ × ℕ) := [(5, 4), (5, 4), (5, 11), (5, 4), (10, 4)]
private abbrev coordinateInput3_58 : LowerPair × Bool × Bool := (([2], [1, 1]), true, true)
private def coordinateCodes3_58 : List (ℕ × ℕ) := [(0, 6), (0, 6), (0, 7), (0, 6), (3, 6)]
private abbrev coordinateInput3_59 : LowerPair × Bool × Bool := (([2], [1, 2]), false, true)
private def coordinateCodes3_59 : List (ℕ × ℕ) := [(5, 8), (5, 26), (5, 8), (10, 8), (5, 8)]
private abbrev coordinateInput3_60 : LowerPair × Bool × Bool := (([2], [1, 2]), true, true)
private def coordinateCodes3_60 : List (ℕ × ℕ) := [(0, 2), (0, 2), (0, 9), (0, 2), (3, 2)]
private abbrev coordinateInput3_61 : LowerPair × Bool × Bool := (([2], [1, 1]), false, true)
private def coordinateCodes3_61 : List (ℕ × ℕ) := [(5, 4), (5, 11), (5, 4), (10, 4), (5, 4)]
private abbrev coordinateInput3_62 : LowerPair × Bool × Bool := (([3], [1]), true, false)
private def coordinateCodes3_62 : List (ℕ × ℕ) := [(16, 1), (16, 2), (16, 1), (17, 1)]
private abbrev coordinateInput3_63 : LowerPair × Bool × Bool := (([3], [1]), false, false)
private def coordinateCodes3_63 : List (ℕ × ℕ) := [(18, 4)]
private abbrev coordinateInput3_64 : LowerPair × Bool × Bool := (([3, 1], [1]), true, false)
private def coordinateCodes3_64 : List (ℕ × ℕ) := [(19, 1), (19, 2), (19, 1), (20, 1), (19, 1)]
private abbrev coordinateInput3_65 : LowerPair × Bool × Bool := (([3, 2], [1]), false, false)
private def coordinateCodes3_65 : List (ℕ × ℕ) := [(21, 4), (21, 4), (21, 11), (21, 4), (24, 4)]
private abbrev coordinateInput3_66 : LowerPair × Bool × Bool := (([3, 2], [1]), true, false)
private def coordinateCodes3_66 : List (ℕ × ℕ) := [(17, 1), (17, 2), (17, 1), (22, 1), (17, 1)]
private abbrev coordinateInput3_67 : LowerPair × Bool × Bool := (([3, 1], [1]), false, false)
private def coordinateCodes3_67 : List (ℕ × ℕ) := [(18, 4), (18, 4)]
private abbrev coordinateInput3_68 : LowerPair × Bool × Bool := (([3], [1, 1]), true, true)
private def coordinateCodes3_68 : List (ℕ × ℕ) := [(16, 6), (16, 6), (16, 7), (16, 6), (17, 6)]
private abbrev coordinateInput3_69 : LowerPair × Bool × Bool := (([3], [1, 2]), false, true)
private def coordinateCodes3_69 : List (ℕ × ℕ) := [(18, 8), (18, 8)]
private abbrev coordinateInput3_70 : LowerPair × Bool × Bool := (([3], [1, 2]), true, true)
private def coordinateCodes3_70 : List (ℕ × ℕ) := [(16, 2), (16, 2), (16, 9), (16, 2), (17, 2)]
private abbrev coordinateInput3_71 : LowerPair × Bool × Bool := (([3], [1, 1]), false, true)
private def coordinateCodes3_71 : List (ℕ × ℕ) := [(18, 4), (18, 4)]
private abbrev coordinateInput3_72 : LowerPair × Bool × Bool := (([2], [3]), true, false)
private def coordinateCodes3_72 : List (ℕ × ℕ) := [(0, 16), (0, 17), (0, 16), (3, 16)]
private abbrev coordinateInput3_73 : LowerPair × Bool × Bool := (([2], [3]), false, false)
private def coordinateCodes3_73 : List (ℕ × ℕ) := [(5, 18)]
private abbrev coordinateInput3_74 : LowerPair × Bool × Bool := (([2, 1], [3]), true, false)
private def coordinateCodes3_74 : List (ℕ × ℕ) := [(12, 16), (12, 17), (12, 16), (13, 16), (12, 16)]
private abbrev coordinateInput3_75 : LowerPair × Bool × Bool := (([2, 2], [3]), false, false)
private def coordinateCodes3_75 : List (ℕ × ℕ) := [(14, 18), (14, 18)]
private abbrev coordinateInput3_76 : LowerPair × Bool × Bool := (([2, 2], [3]), true, false)
private def coordinateCodes3_76 : List (ℕ × ℕ) := [(3, 16), (3, 17), (3, 16), (15, 16), (3, 16)]
private abbrev coordinateInput3_77 : LowerPair × Bool × Bool := (([2, 1], [3]), false, false)
private def coordinateCodes3_77 : List (ℕ × ℕ) := [(5, 18), (5, 18)]
private abbrev coordinateInput3_78 : LowerPair × Bool × Bool := (([2], [3, 1]), true, true)
private def coordinateCodes3_78 : List (ℕ × ℕ) := [(0, 19), (0, 19), (0, 20), (0, 19), (3, 19)]
private abbrev coordinateInput3_79 : LowerPair × Bool × Bool := (([2], [3, 2]), false, true)
private def coordinateCodes3_79 : List (ℕ × ℕ) := [(5, 21), (5, 24), (5, 21), (10, 21), (5, 21)]
private abbrev coordinateInput3_80 : LowerPair × Bool × Bool := (([2], [3, 2]), true, true)
private def coordinateCodes3_80 : List (ℕ × ℕ) := [(0, 17), (0, 17), (0, 22), (0, 17), (3, 17)]
private abbrev coordinateInput3_81 : LowerPair × Bool × Bool := (([2], [3, 1]), false, true)
private def coordinateCodes3_81 : List (ℕ × ℕ) := [(5, 18), (5, 18)]
private abbrev coordinateInput3_82 : LowerPair × Bool × Bool := (([3], [1, 1]), true, false)
private def coordinateCodes3_82 : List (ℕ × ℕ) := [(16, 6), (16, 6), (16, 7), (16, 6), (17, 6)]
private abbrev coordinateInput3_83 : LowerPair × Bool × Bool := (([3], [1, 1]), false, false)
private def coordinateCodes3_83 : List (ℕ × ℕ) := [(18, 4), (18, 4)]
private abbrev coordinateInput3_84 : LowerPair × Bool × Bool := (([3, 1], [1, 1]), true, false)
private def coordinateCodes3_84 : List (ℕ × ℕ) := [(19, 6), (19, 7), (19, 6), (20, 6)]
private abbrev coordinateInput3_85 : LowerPair × Bool × Bool := (([3, 2], [1, 1]), false, false)
private def coordinateCodes3_85 : List (ℕ × ℕ) := [(21, 4), (21, 11), (21, 4), (24, 4)]
private abbrev coordinateInput3_86 : LowerPair × Bool × Bool := (([3, 2], [1, 1]), true, false)
private def coordinateCodes3_86 : List (ℕ × ℕ) := [(17, 6), (17, 7), (17, 6), (22, 6)]
private abbrev coordinateInput3_87 : LowerPair × Bool × Bool := (([3, 1], [1, 1]), false, false)
private def coordinateCodes3_87 : List (ℕ × ℕ) := [(18, 4)]
private abbrev coordinateInput3_88 : LowerPair × Bool × Bool := (([3], [1, 1, 1]), true, true)
private def coordinateCodes3_88 : List (ℕ × ℕ) := [(16, 6), (16, 7), (16, 6), (17, 6)]
private abbrev coordinateInput3_89 : LowerPair × Bool × Bool := (([3], [1, 1, 2]), false, true)
private def coordinateCodes3_89 : List (ℕ × ℕ) := [(18, 11)]
private abbrev coordinateInput3_90 : LowerPair × Bool × Bool := (([3], [1, 1, 2]), true, true)
private def coordinateCodes3_90 : List (ℕ × ℕ) := [(16, 27), (16, 28), (16, 27), (17, 27)]
private abbrev coordinateInput3_91 : LowerPair × Bool × Bool := (([3], [1, 1, 1]), false, true)
private def coordinateCodes3_91 : List (ℕ × ℕ) := [(18, 29)]

private def decodeCoordinate3 (x : ℕ × ℕ) : CertField × CertField :=
  (coordinateFields3[x.1]?.getD ⟨0,0,0,0⟩,coordinateFields3[x.2]?.getD ⟨0,0,0,0⟩)

private theorem hCoordinate3_0 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_0.1 coordinateInput3_0.2.1 coordinateInput3_0.2.2).map Prod.fst = coordinateCodes3_0.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_1 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_1.1 coordinateInput3_1.2.1 coordinateInput3_1.2.2).map Prod.fst = coordinateCodes3_1.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_2 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_2.1 coordinateInput3_2.2.1 coordinateInput3_2.2.2).map Prod.fst = coordinateCodes3_2.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_3 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_3.1 coordinateInput3_3.2.1 coordinateInput3_3.2.2).map Prod.fst = coordinateCodes3_3.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_4 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_4.1 coordinateInput3_4.2.1 coordinateInput3_4.2.2).map Prod.fst = coordinateCodes3_4.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_5 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_5.1 coordinateInput3_5.2.1 coordinateInput3_5.2.2).map Prod.fst = coordinateCodes3_5.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_6 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_6.1 coordinateInput3_6.2.1 coordinateInput3_6.2.2).map Prod.fst = coordinateCodes3_6.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_7 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_7.1 coordinateInput3_7.2.1 coordinateInput3_7.2.2).map Prod.fst = coordinateCodes3_7.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_8 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_8.1 coordinateInput3_8.2.1 coordinateInput3_8.2.2).map Prod.fst = coordinateCodes3_8.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_9 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_9.1 coordinateInput3_9.2.1 coordinateInput3_9.2.2).map Prod.fst = coordinateCodes3_9.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_10 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_10.1 coordinateInput3_10.2.1 coordinateInput3_10.2.2).map Prod.fst = coordinateCodes3_10.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_11 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_11.1 coordinateInput3_11.2.1 coordinateInput3_11.2.2).map Prod.fst = coordinateCodes3_11.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_12 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_12.1 coordinateInput3_12.2.1 coordinateInput3_12.2.2).map Prod.fst = coordinateCodes3_12.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_13 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_13.1 coordinateInput3_13.2.1 coordinateInput3_13.2.2).map Prod.fst = coordinateCodes3_13.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_14 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_14.1 coordinateInput3_14.2.1 coordinateInput3_14.2.2).map Prod.fst = coordinateCodes3_14.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_15 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_15.1 coordinateInput3_15.2.1 coordinateInput3_15.2.2).map Prod.fst = coordinateCodes3_15.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_16 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_16.1 coordinateInput3_16.2.1 coordinateInput3_16.2.2).map Prod.fst = coordinateCodes3_16.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_17 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_17.1 coordinateInput3_17.2.1 coordinateInput3_17.2.2).map Prod.fst = coordinateCodes3_17.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_18 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_18.1 coordinateInput3_18.2.1 coordinateInput3_18.2.2).map Prod.fst = coordinateCodes3_18.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_19 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_19.1 coordinateInput3_19.2.1 coordinateInput3_19.2.2).map Prod.fst = coordinateCodes3_19.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_20 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_20.1 coordinateInput3_20.2.1 coordinateInput3_20.2.2).map Prod.fst = coordinateCodes3_20.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_21 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_21.1 coordinateInput3_21.2.1 coordinateInput3_21.2.2).map Prod.fst = coordinateCodes3_21.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_22 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_22.1 coordinateInput3_22.2.1 coordinateInput3_22.2.2).map Prod.fst = coordinateCodes3_22.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_23 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_23.1 coordinateInput3_23.2.1 coordinateInput3_23.2.2).map Prod.fst = coordinateCodes3_23.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_24 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_24.1 coordinateInput3_24.2.1 coordinateInput3_24.2.2).map Prod.fst = coordinateCodes3_24.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_25 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_25.1 coordinateInput3_25.2.1 coordinateInput3_25.2.2).map Prod.fst = coordinateCodes3_25.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_26 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_26.1 coordinateInput3_26.2.1 coordinateInput3_26.2.2).map Prod.fst = coordinateCodes3_26.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_27 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_27.1 coordinateInput3_27.2.1 coordinateInput3_27.2.2).map Prod.fst = coordinateCodes3_27.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_28 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_28.1 coordinateInput3_28.2.1 coordinateInput3_28.2.2).map Prod.fst = coordinateCodes3_28.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_29 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_29.1 coordinateInput3_29.2.1 coordinateInput3_29.2.2).map Prod.fst = coordinateCodes3_29.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_30 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_30.1 coordinateInput3_30.2.1 coordinateInput3_30.2.2).map Prod.fst = coordinateCodes3_30.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_31 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_31.1 coordinateInput3_31.2.1 coordinateInput3_31.2.2).map Prod.fst = coordinateCodes3_31.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_32 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_32.1 coordinateInput3_32.2.1 coordinateInput3_32.2.2).map Prod.fst = coordinateCodes3_32.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_33 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_33.1 coordinateInput3_33.2.1 coordinateInput3_33.2.2).map Prod.fst = coordinateCodes3_33.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_34 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_34.1 coordinateInput3_34.2.1 coordinateInput3_34.2.2).map Prod.fst = coordinateCodes3_34.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_35 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_35.1 coordinateInput3_35.2.1 coordinateInput3_35.2.2).map Prod.fst = coordinateCodes3_35.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_36 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_36.1 coordinateInput3_36.2.1 coordinateInput3_36.2.2).map Prod.fst = coordinateCodes3_36.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_37 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_37.1 coordinateInput3_37.2.1 coordinateInput3_37.2.2).map Prod.fst = coordinateCodes3_37.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_38 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_38.1 coordinateInput3_38.2.1 coordinateInput3_38.2.2).map Prod.fst = coordinateCodes3_38.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_39 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_39.1 coordinateInput3_39.2.1 coordinateInput3_39.2.2).map Prod.fst = coordinateCodes3_39.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_40 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_40.1 coordinateInput3_40.2.1 coordinateInput3_40.2.2).map Prod.fst = coordinateCodes3_40.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_41 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_41.1 coordinateInput3_41.2.1 coordinateInput3_41.2.2).map Prod.fst = coordinateCodes3_41.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_42 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_42.1 coordinateInput3_42.2.1 coordinateInput3_42.2.2).map Prod.fst = coordinateCodes3_42.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_43 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_43.1 coordinateInput3_43.2.1 coordinateInput3_43.2.2).map Prod.fst = coordinateCodes3_43.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_44 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_44.1 coordinateInput3_44.2.1 coordinateInput3_44.2.2).map Prod.fst = coordinateCodes3_44.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_45 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_45.1 coordinateInput3_45.2.1 coordinateInput3_45.2.2).map Prod.fst = coordinateCodes3_45.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_46 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_46.1 coordinateInput3_46.2.1 coordinateInput3_46.2.2).map Prod.fst = coordinateCodes3_46.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_47 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_47.1 coordinateInput3_47.2.1 coordinateInput3_47.2.2).map Prod.fst = coordinateCodes3_47.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_48 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_48.1 coordinateInput3_48.2.1 coordinateInput3_48.2.2).map Prod.fst = coordinateCodes3_48.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_49 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_49.1 coordinateInput3_49.2.1 coordinateInput3_49.2.2).map Prod.fst = coordinateCodes3_49.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_50 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_50.1 coordinateInput3_50.2.1 coordinateInput3_50.2.2).map Prod.fst = coordinateCodes3_50.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_51 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_51.1 coordinateInput3_51.2.1 coordinateInput3_51.2.2).map Prod.fst = coordinateCodes3_51.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_52 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_52.1 coordinateInput3_52.2.1 coordinateInput3_52.2.2).map Prod.fst = coordinateCodes3_52.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_53 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_53.1 coordinateInput3_53.2.1 coordinateInput3_53.2.2).map Prod.fst = coordinateCodes3_53.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_54 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_54.1 coordinateInput3_54.2.1 coordinateInput3_54.2.2).map Prod.fst = coordinateCodes3_54.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_55 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_55.1 coordinateInput3_55.2.1 coordinateInput3_55.2.2).map Prod.fst = coordinateCodes3_55.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_56 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_56.1 coordinateInput3_56.2.1 coordinateInput3_56.2.2).map Prod.fst = coordinateCodes3_56.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_57 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_57.1 coordinateInput3_57.2.1 coordinateInput3_57.2.2).map Prod.fst = coordinateCodes3_57.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_58 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_58.1 coordinateInput3_58.2.1 coordinateInput3_58.2.2).map Prod.fst = coordinateCodes3_58.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_59 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_59.1 coordinateInput3_59.2.1 coordinateInput3_59.2.2).map Prod.fst = coordinateCodes3_59.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_60 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_60.1 coordinateInput3_60.2.1 coordinateInput3_60.2.2).map Prod.fst = coordinateCodes3_60.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_61 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_61.1 coordinateInput3_61.2.1 coordinateInput3_61.2.2).map Prod.fst = coordinateCodes3_61.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_62 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_62.1 coordinateInput3_62.2.1 coordinateInput3_62.2.2).map Prod.fst = coordinateCodes3_62.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_63 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_63.1 coordinateInput3_63.2.1 coordinateInput3_63.2.2).map Prod.fst = coordinateCodes3_63.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_64 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_64.1 coordinateInput3_64.2.1 coordinateInput3_64.2.2).map Prod.fst = coordinateCodes3_64.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_65 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_65.1 coordinateInput3_65.2.1 coordinateInput3_65.2.2).map Prod.fst = coordinateCodes3_65.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_66 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_66.1 coordinateInput3_66.2.1 coordinateInput3_66.2.2).map Prod.fst = coordinateCodes3_66.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_67 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_67.1 coordinateInput3_67.2.1 coordinateInput3_67.2.2).map Prod.fst = coordinateCodes3_67.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_68 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_68.1 coordinateInput3_68.2.1 coordinateInput3_68.2.2).map Prod.fst = coordinateCodes3_68.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_69 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_69.1 coordinateInput3_69.2.1 coordinateInput3_69.2.2).map Prod.fst = coordinateCodes3_69.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_70 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_70.1 coordinateInput3_70.2.1 coordinateInput3_70.2.2).map Prod.fst = coordinateCodes3_70.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_71 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_71.1 coordinateInput3_71.2.1 coordinateInput3_71.2.2).map Prod.fst = coordinateCodes3_71.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_72 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_72.1 coordinateInput3_72.2.1 coordinateInput3_72.2.2).map Prod.fst = coordinateCodes3_72.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_73 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_73.1 coordinateInput3_73.2.1 coordinateInput3_73.2.2).map Prod.fst = coordinateCodes3_73.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_74 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_74.1 coordinateInput3_74.2.1 coordinateInput3_74.2.2).map Prod.fst = coordinateCodes3_74.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_75 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_75.1 coordinateInput3_75.2.1 coordinateInput3_75.2.2).map Prod.fst = coordinateCodes3_75.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_76 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_76.1 coordinateInput3_76.2.1 coordinateInput3_76.2.2).map Prod.fst = coordinateCodes3_76.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_77 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_77.1 coordinateInput3_77.2.1 coordinateInput3_77.2.2).map Prod.fst = coordinateCodes3_77.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_78 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_78.1 coordinateInput3_78.2.1 coordinateInput3_78.2.2).map Prod.fst = coordinateCodes3_78.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_79 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_79.1 coordinateInput3_79.2.1 coordinateInput3_79.2.2).map Prod.fst = coordinateCodes3_79.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_80 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_80.1 coordinateInput3_80.2.1 coordinateInput3_80.2.2).map Prod.fst = coordinateCodes3_80.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_81 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_81.1 coordinateInput3_81.2.1 coordinateInput3_81.2.2).map Prod.fst = coordinateCodes3_81.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_82 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_82.1 coordinateInput3_82.2.1 coordinateInput3_82.2.2).map Prod.fst = coordinateCodes3_82.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_83 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_83.1 coordinateInput3_83.2.1 coordinateInput3_83.2.2).map Prod.fst = coordinateCodes3_83.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_84 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_84.1 coordinateInput3_84.2.1 coordinateInput3_84.2.2).map Prod.fst = coordinateCodes3_84.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_85 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_85.1 coordinateInput3_85.2.1 coordinateInput3_85.2.2).map Prod.fst = coordinateCodes3_85.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_86 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_86.1 coordinateInput3_86.2.1 coordinateInput3_86.2.2).map Prod.fst = coordinateCodes3_86.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_87 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_87.1 coordinateInput3_87.2.1 coordinateInput3_87.2.2).map Prod.fst = coordinateCodes3_87.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_88 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_88.1 coordinateInput3_88.2.1 coordinateInput3_88.2.2).map Prod.fst = coordinateCodes3_88.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_89 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_89.1 coordinateInput3_89.2.1 coordinateInput3_89.2.2).map Prod.fst = coordinateCodes3_89.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_90 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_90.1 coordinateInput3_90.2.1 coordinateInput3_90.2.2).map Prod.fst = coordinateCodes3_90.map decodeCoordinate3 := by decide +kernel

private theorem hCoordinate3_91 :
    (trunkEndpointCases (trunkCatalog.states 3).context coordinateInput3_91.1 coordinateInput3_91.2.1 coordinateInput3_91.2.2).map Prod.fst = coordinateCodes3_91.map decodeCoordinate3 := by decide +kernel

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
(0,[1,13,15,17,19,20,32,34,36,38,40,52,54,56,58,60,72,74,76,78,80,92,94,96,98],0,[-1]),
(0,[2,3,4,5,6,7,8,9,10,11,22,23,24,25,26,27,28,29,30,31,42,43,44,45,46,47,48,49,50,51,62,63,64,65,66,67,68,69,70,71,82,83,84,85,86,87,88,89,90,91],0,[-1]),
(0,[12],0,[-1]),
(0,[14],0,[-1]),
(0,[16],0,[-1]),
(0,[18],0,[-1]),
(0,[21],2,[0,1,2,3]),
(0,[21,41],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[21,41,53],7,[0,1,2,3]),
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
(0,[53],2,[0,1,2,3]),
(0,[53],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[53],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[53],12,[0,1,2,3]),
(0,[53],15,[0,1,2,3]),
(0,[53],17,[0,1,2,3,4,5,6,7,8,9]),
(0,[53],19,[0,1,2,3,4,5,6,7,8,9]),
(0,[53],20,[8,10,11,16,17,18]),
(0,[55,75,95],0,[-1]),
(0,[57,77,97],0,[-1]),
(0,[59,79,99],0,[-1]),
(0,[61],0,[-1]),
(0,[73],0,[-1]),
(0,[81],0,[-1]),
(0,[93],0,[-1]),
(1,[0,12,14],0,[-1]),
(1,[1,13,15,17,19,20,32,34,36,38,40,52,54,56,58,60,72,74,76,78,80,92,94,96,98],0,[-1]),
(1,[2,3,4,5,6,7,8,9,10,11,22,23,24,25,26,27,28,29,30,31,42,43,44,45,46,47,48,49,50,51,62,63,64,65,66,67,68,69,70,71,82,83,84,85,86,87,88,89,90,91],0,[-1]),
(1,[16],0,[-1]),
(1,[18],0,[-1]),
(1,[21,33,35],0,[-1]),
(1,[37],0,[-1]),
(1,[39],0,[-1]),
(1,[41,61,81],0,[-1]),
(1,[53,55],0,[-1]),
(1,[57],0,[-1]),
(1,[59],0,[-1]),
(1,[73,75],0,[-1]),
(1,[77],0,[-1]),
(1,[79],0,[-1]),
(1,[93,95],0,[-1]),
(1,[97],0,[-1]),
(1,[99],0,[-1]),
(2,[0,12],0,[-1]),
(2,[1,13,15,17,19,20,32,34,36,38,40,52,54,56,58,60,72,74,76,78,80,92,94,96,98],0,[-1]),
(2,[2,3,4,5,6,7,8,9,10,11,22,23,24,25,26,27,28,29,30,31,42,43,44,45,46,47,48,49,50,51,62,63,64,65,66,67,68,69,70,71,82,83,84,85,86,87,88,89,90,91],0,[-1]),
(2,[14],0,[-1]),
(2,[16],0,[-1]),
(2,[18],0,[-1]),
(2,[21,33],0,[-1]),
(2,[35],0,[-1]),
(2,[37],0,[-1]),
(2,[39],0,[-1]),
(2,[41],2,[0,1,2,3]),
(2,[41],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[41,53,73,75,93],7,[0,1,2,3]),
(2,[41],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[41,53],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[41],14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[41,53],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[41],19,[0,1,2,3,4,5,6,7,8,9]),
(2,[41],22,[0,1,2,3,4,5,6,7,8,9]),
(2,[41],25,[8,10,11,16,17,18]),
(2,[53,73,75,93],2,[0,1,2,3]),
(2,[53],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[53],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[53],14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[53],19,[0,1,2,3,4,5,6,7,8,9]),
(2,[53],22,[0,1,2,3,4,5,6,7,8,9]),
(2,[53,73,75,93],25,[8,10,11,16,17,18]),
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
(2,[73,75],22,[0,1,2,3,4,5,6,7,8,9]),
(2,[75],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[75],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[75],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[75],14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[75],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[75],19,[0,1,2,3,4,5,6,7,8,9]),
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
(3,[0,12,14],0,[-1]),
(3,[1,13,15,17,19,20,32,34,36,38,40,52,54,56,58,60,72,74,76,78,80,92,94,96,98],0,[-1]),
(3,[2,3,4,5,6,7,8,9,10,11,22,23,24,25,26,27,28,29,30,31,42,43,44,45,46,47,48,49,50,51,62,63,64,65,66,67,68,69,70,71,82,83,84,85,86,87,88,89,90,91],0,[-1]),
(3,[16],0,[-1]),
(3,[18],0,[-1]),
(3,[21,33,35],0,[-1]),
(3,[37],0,[-1]),
(3,[39],0,[-1]),
(3,[41,61,81],0,[-1]),
(3,[53,55],0,[-1]),
(3,[57],0,[-1]),
(3,[59],0,[-1]),
(3,[73,75,79],2,[0,1,2,3]),
(3,[73],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[73,75,79],7,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[73],9,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[73,75],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[73],14,[0,1,2,3,4,5,6,7,8,9]),
(3,[73,75],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[73],19,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[73,75],22,[0,1,2,3,4,5,6,7,8,9]),
(3,[73],24,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[73,75],27,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[73],29,[0,1,2,3,4,5,6,7,8,9]),
(3,[73,75,79],32,[0,1,2,3,4,5,6,7]),
(3,[73,75],34,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[73,75],35,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[73],36,[0,1,2,3]),
(3,[73],38,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[73],39,[0,1,2,3]),
(3,[73,75],40,[0,1,2,3]),
(3,[73,75],41,[8,10,11,16,17,18]),
(3,[75],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[75],9,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[75],14,[0,1,2,3,4,5,6,7,8,9]),
(3,[75],19,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[75],24,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[75],29,[0,1,2,3,4,5,6,7,8,9]),
(3,[75],36,[0,1,2,3]),
(3,[75],38,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[75],39,[0,1,2,3]),
(3,[77],0,[-1]),
(3,[79],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[79],9,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[79],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[79],14,[0,1,2,3,4,5,6,7,8,9]),
(3,[79],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[79],19,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[79],22,[0,1,2,3,4,5,6,7,8,9]),
(3,[79],24,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[79],27,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[79],29,[0,1,2,3,4,5,6,7,8,9]),
(3,[79],34,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[79],35,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[79],36,[0,1,2,3]),
(3,[79],38,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[79],39,[0,1,2,3]),
(3,[79],40,[0,1,2,3]),
(3,[79],41,[8,10,11,16,17,18]),
(3,[93],0,[-1]),
(3,[95],0,[-1]),
(3,[97],0,[-1]),
(3,[99],0,[-1]),
(4,[0,12,14,18],0,[-1]),
(4,[1,13,15,17,19,20,32,34,36,38,40,52,54,56,58,60,72,74,76,78,80,92,94,96,98],0,[-1]),
(4,[2,3,4,5,6,7,8,9,10,11,22,23,24,25,26,27,28,29,30,31,42,43,44,45,46,47,48,49,50,51,62,63,64,65,66,67,68,69,70,71,82,83,84,85,86,87,88,89,90,91],0,[-1]),
(4,[16],0,[-1]),
(4,[21,33,35,39],0,[-1]),
(4,[37],0,[-1]),
(4,[41,61,81],0,[-1]),
(4,[53,55,59],0,[-1]),
(4,[57],0,[-1]),
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
(4,[93,95,99],0,[-1]),
(4,[97],0,[-1])]
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
private abbrev specAt3 (pi goal : ℕ) : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) pi))[goal-1]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private abbrev cSpec3_0_1 := specAt3 0 1
private theorem cFlags3_0_1 : automaticFlags (trunkCatalog.states 3).context cSpec3_0_1 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_2 coordinateInput3_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_2 hCoordinate3_1]
  decide +kernel
private abbrev cSpec3_0_2 := specAt3 0 2
private theorem cFlags3_0_2 : automaticFlags (trunkCatalog.states 3).context cSpec3_0_2 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_4 coordinateInput3_5 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_4 hCoordinate3_5]
  decide +kernel
private abbrev cSpec3_0_3 := specAt3 0 3
private theorem cFlags3_0_3 : automaticFlags (trunkCatalog.states 3).context cSpec3_0_3 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_6 coordinateInput3_7 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_6 hCoordinate3_7]
  decide +kernel
private abbrev cSpec3_0_4 := specAt3 0 4
private theorem cFlags3_0_4 : automaticFlags (trunkCatalog.states 3).context cSpec3_0_4 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_8 coordinateInput3_9 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_8 hCoordinate3_9]
  decide +kernel
private abbrev cSpec3_0_5 := specAt3 0 5
private theorem cFlags3_0_5 : automaticFlags (trunkCatalog.states 3).context cSpec3_0_5 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_10 coordinateInput3_11 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_10 hCoordinate3_11]
  decide +kernel
private abbrev cSpec3_0_6 := specAt3 0 6
private theorem cFlags3_0_6 : automaticFlags (trunkCatalog.states 3).context cSpec3_0_6 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_0 coordinateInput3_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_0 hCoordinate3_3]
  decide +kernel
private abbrev cSpec3_0_7 := specAt3 0 7
private theorem cFlags3_0_7 : automaticFlags (trunkCatalog.states 3).context cSpec3_0_7 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_12 coordinateInput3_13 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_12 hCoordinate3_13]
  decide +kernel
private abbrev cSpec3_0_8 := specAt3 0 8
private theorem cFlags3_0_8 : automaticFlags (trunkCatalog.states 3).context cSpec3_0_8 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_14 coordinateInput3_15 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_14 hCoordinate3_15]
  decide +kernel
private abbrev cSpec3_0_9 := specAt3 0 9
private theorem cFlags3_0_9 : automaticFlags (trunkCatalog.states 3).context cSpec3_0_9 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_16 coordinateInput3_17 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_16 hCoordinate3_17]
  decide +kernel
private abbrev cSpec3_0_10 := specAt3 0 10
private theorem cFlags3_0_10 : automaticFlags (trunkCatalog.states 3).context cSpec3_0_10 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_18 coordinateInput3_19 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_18 hCoordinate3_19]
  decide +kernel
private abbrev cSpec3_0_11 := specAt3 0 11
private theorem cFlags3_0_11 : automaticFlags (trunkCatalog.states 3).context cSpec3_0_11 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_20 coordinateInput3_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_20 hCoordinate3_21]
  decide +kernel
private abbrev cSpec3_0_12 := specAt3 0 12
private theorem cFlags3_0_12 : automaticFlags (trunkCatalog.states 3).context cSpec3_0_12 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_22 coordinateInput3_23 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_22 hCoordinate3_23]
  decide +kernel
private abbrev cSpec3_0_13 := specAt3 0 13
private theorem cFlags3_0_13 : automaticFlags (trunkCatalog.states 3).context cSpec3_0_13 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_24 coordinateInput3_25 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_24 hCoordinate3_25]
  decide +kernel
private abbrev cSpec3_0_14 := specAt3 0 14
private theorem cFlags3_0_14 : automaticFlags (trunkCatalog.states 3).context cSpec3_0_14 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_26 coordinateInput3_27 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_26 hCoordinate3_27]
  decide +kernel
private abbrev cSpec3_0_15 := specAt3 0 15
private theorem cFlags3_0_15 : automaticFlags (trunkCatalog.states 3).context cSpec3_0_15 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_28 coordinateInput3_29 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_28 hCoordinate3_29]
  decide +kernel
private abbrev cSpec3_0_16 := specAt3 0 16
private theorem cFlags3_0_16 : automaticFlags (trunkCatalog.states 3).context cSpec3_0_16 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_2 coordinateInput3_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_2 hCoordinate3_3]
  decide +kernel
private abbrev cSpec3_0_17 := specAt3 0 17
private theorem cFlags3_0_17 : automaticFlags (trunkCatalog.states 3).context cSpec3_0_17 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_0 coordinateInput3_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_0 hCoordinate3_1]
  decide +kernel
private abbrev cSpec3_0_18 := specAt3 0 18
private theorem cFlags3_0_18 : automaticFlags (trunkCatalog.states 3).context cSpec3_0_18 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_0 coordinateInput3_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_0 hCoordinate3_21]
  decide +kernel
private abbrev cSpec3_0_19 := specAt3 0 19
private theorem cFlags3_0_19 : automaticFlags (trunkCatalog.states 3).context cSpec3_0_19 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_20 coordinateInput3_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_20 hCoordinate3_3]
  decide +kernel
private abbrev cSpec3_0_20 := specAt3 0 20
private theorem cFlags3_0_20 : automaticFlags (trunkCatalog.states 3).context cSpec3_0_20 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  rw [automaticFlags_cached _ _ coordinateInput3_2 coordinateInput3_30 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_2 hCoordinate3_30]
  decide +kernel
private abbrev cSpec3_0_21 := specAt3 0 21
private theorem cFlags3_0_21 : automaticFlags (trunkCatalog.states 3).context cSpec3_0_21 = (List.replicate 2 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_31 coordinateInput3_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_31 hCoordinate3_21]
  decide +kernel
private abbrev cSpec3_1_1 := specAt3 1 1
private theorem cFlags3_1_1 : automaticFlags (trunkCatalog.states 3).context cSpec3_1_1 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec3_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_1

private abbrev cSpec3_1_2 := specAt3 1 2
private theorem cFlags3_1_2 : automaticFlags (trunkCatalog.states 3).context cSpec3_1_2 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec3_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_2

private abbrev cSpec3_1_3 := specAt3 1 3
private theorem cFlags3_1_3 : automaticFlags (trunkCatalog.states 3).context cSpec3_1_3 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec3_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_3

private abbrev cSpec3_1_4 := specAt3 1 4
private theorem cFlags3_1_4 : automaticFlags (trunkCatalog.states 3).context cSpec3_1_4 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec3_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_4

private abbrev cSpec3_1_5 := specAt3 1 5
private theorem cFlags3_1_5 : automaticFlags (trunkCatalog.states 3).context cSpec3_1_5 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec3_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_5

private abbrev cSpec3_1_6 := specAt3 1 6
private theorem cFlags3_1_6 : automaticFlags (trunkCatalog.states 3).context cSpec3_1_6 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec3_0_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_6

private abbrev cSpec3_1_7 := specAt3 1 7
private theorem cFlags3_1_7 : automaticFlags (trunkCatalog.states 3).context cSpec3_1_7 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec3_0_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_7

private abbrev cSpec3_1_8 := specAt3 1 8
private theorem cFlags3_1_8 : automaticFlags (trunkCatalog.states 3).context cSpec3_1_8 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec3_0_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_8

private abbrev cSpec3_1_9 := specAt3 1 9
private theorem cFlags3_1_9 : automaticFlags (trunkCatalog.states 3).context cSpec3_1_9 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec3_0_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_9

private abbrev cSpec3_1_10 := specAt3 1 10
private theorem cFlags3_1_10 : automaticFlags (trunkCatalog.states 3).context cSpec3_1_10 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec3_0_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_10

private abbrev cSpec3_1_11 := specAt3 1 11
private theorem cFlags3_1_11 : automaticFlags (trunkCatalog.states 3).context cSpec3_1_11 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_32 coordinateInput3_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_32 hCoordinate3_33]
  decide +kernel
private abbrev cSpec3_1_12 := specAt3 1 12
private theorem cFlags3_1_12 : automaticFlags (trunkCatalog.states 3).context cSpec3_1_12 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_34 coordinateInput3_35 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_34 hCoordinate3_35]
  decide +kernel
private abbrev cSpec3_1_13 := specAt3 1 13
private theorem cFlags3_1_13 : automaticFlags (trunkCatalog.states 3).context cSpec3_1_13 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_36 coordinateInput3_37 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_36 hCoordinate3_37]
  decide +kernel
private abbrev cSpec3_1_14 := specAt3 1 14
private theorem cFlags3_1_14 : automaticFlags (trunkCatalog.states 3).context cSpec3_1_14 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_38 coordinateInput3_39 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_38 hCoordinate3_39]
  decide +kernel
private abbrev cSpec3_1_15 := specAt3 1 15
private theorem cFlags3_1_15 : automaticFlags (trunkCatalog.states 3).context cSpec3_1_15 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_40 coordinateInput3_41 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_40 hCoordinate3_41]
  decide +kernel
private abbrev cSpec3_1_16 := specAt3 1 16
private theorem cFlags3_1_16 : automaticFlags (trunkCatalog.states 3).context cSpec3_1_16 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec3_0_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_16

private abbrev cSpec3_1_17 := specAt3 1 17
private theorem cFlags3_1_17 : automaticFlags (trunkCatalog.states 3).context cSpec3_1_17 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec3_0_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_17

private abbrev cSpec3_1_18 := specAt3 1 18
private theorem cFlags3_1_18 : automaticFlags (trunkCatalog.states 3).context cSpec3_1_18 = (List.replicate 5 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_0 coordinateInput3_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_0 hCoordinate3_33]
  decide +kernel
private abbrev cSpec3_1_19 := specAt3 1 19
private theorem cFlags3_1_19 : automaticFlags (trunkCatalog.states 3).context cSpec3_1_19 = (List.replicate 8 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_32 coordinateInput3_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_32 hCoordinate3_3]
  decide +kernel
private abbrev cSpec3_1_20 := specAt3 1 20
private theorem cFlags3_1_20 : automaticFlags (trunkCatalog.states 3).context cSpec3_1_20 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  exact (automaticFlags_same _ _ cSpec3_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_20

private abbrev cSpec3_1_21 := specAt3 1 21
private theorem cFlags3_1_21 : automaticFlags (trunkCatalog.states 3).context cSpec3_1_21 = (List.replicate 1 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_31 coordinateInput3_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_31 hCoordinate3_33]
  decide +kernel
private abbrev cSpec3_2_1 := specAt3 2 1
private theorem cFlags3_2_1 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_1 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec3_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_1

private abbrev cSpec3_2_2 := specAt3 2 2
private theorem cFlags3_2_2 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_2 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec3_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_2

private abbrev cSpec3_2_3 := specAt3 2 3
private theorem cFlags3_2_3 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_3 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec3_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_3

private abbrev cSpec3_2_4 := specAt3 2 4
private theorem cFlags3_2_4 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_4 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec3_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_4

private abbrev cSpec3_2_5 := specAt3 2 5
private theorem cFlags3_2_5 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_5 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec3_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_5

private abbrev cSpec3_2_6 := specAt3 2 6
private theorem cFlags3_2_6 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_6 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec3_0_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_6

private abbrev cSpec3_2_7 := specAt3 2 7
private theorem cFlags3_2_7 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_7 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec3_0_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_7

private abbrev cSpec3_2_8 := specAt3 2 8
private theorem cFlags3_2_8 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_8 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec3_0_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_8

private abbrev cSpec3_2_9 := specAt3 2 9
private theorem cFlags3_2_9 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_9 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec3_0_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_9

private abbrev cSpec3_2_10 := specAt3 2 10
private theorem cFlags3_2_10 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_10 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec3_0_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_10

private abbrev cSpec3_2_11 := specAt3 2 11
private theorem cFlags3_2_11 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_11 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_42 coordinateInput3_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_42 hCoordinate3_43]
  decide +kernel
private abbrev cSpec3_2_12 := specAt3 2 12
private theorem cFlags3_2_12 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_12 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_44 coordinateInput3_45 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_44 hCoordinate3_45]
  decide +kernel
private abbrev cSpec3_2_13 := specAt3 2 13
private theorem cFlags3_2_13 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_13 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_46 coordinateInput3_47 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_46 hCoordinate3_47]
  decide +kernel
private abbrev cSpec3_2_14 := specAt3 2 14
private theorem cFlags3_2_14 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_14 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_48 coordinateInput3_49 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_48 hCoordinate3_49]
  decide +kernel
private abbrev cSpec3_2_15 := specAt3 2 15
private theorem cFlags3_2_15 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_15 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_50 coordinateInput3_51 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_50 hCoordinate3_51]
  decide +kernel
private abbrev cSpec3_2_16 := specAt3 2 16
private theorem cFlags3_2_16 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_16 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec3_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_1_11

private abbrev cSpec3_2_17 := specAt3 2 17
private theorem cFlags3_2_17 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec3_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_1_12

private abbrev cSpec3_2_18 := specAt3 2 18
private theorem cFlags3_2_18 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_18 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec3_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_1_13

private abbrev cSpec3_2_19 := specAt3 2 19
private theorem cFlags3_2_19 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_19 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec3_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_1_14

private abbrev cSpec3_2_20 := specAt3 2 20
private theorem cFlags3_2_20 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_20 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec3_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_1_15

private abbrev cSpec3_2_21 := specAt3 2 21
private theorem cFlags3_2_21 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_21 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec3_0_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_16

private abbrev cSpec3_2_22 := specAt3 2 22
private theorem cFlags3_2_22 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_22 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec3_0_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_17

private abbrev cSpec3_2_23 := specAt3 2 23
private theorem cFlags3_2_23 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_23 = (List.replicate 20 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_0 coordinateInput3_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_0 hCoordinate3_43]
  decide +kernel
private abbrev cSpec3_2_24 := specAt3 2 24
private theorem cFlags3_2_24 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_24 = (List.replicate 8 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_42 coordinateInput3_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_42 hCoordinate3_3]
  decide +kernel
private abbrev cSpec3_2_25 := specAt3 2 25
private theorem cFlags3_2_25 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_25 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  exact (automaticFlags_same _ _ cSpec3_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_20

private abbrev cSpec3_2_26 := specAt3 2 26
private theorem cFlags3_2_26 : automaticFlags (trunkCatalog.states 3).context cSpec3_2_26 = (List.replicate 1 true) := by
  exact (automaticFlags_same _ _ cSpec3_1_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_1_21

private abbrev cSpec3_3_1 := specAt3 3 1
private theorem cFlags3_3_1 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_1 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec3_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_1

private abbrev cSpec3_3_2 := specAt3 3 2
private theorem cFlags3_3_2 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_2 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec3_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_2

private abbrev cSpec3_3_3 := specAt3 3 3
private theorem cFlags3_3_3 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_3 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec3_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_3

private abbrev cSpec3_3_4 := specAt3 3 4
private theorem cFlags3_3_4 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_4 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec3_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_4

private abbrev cSpec3_3_5 := specAt3 3 5
private theorem cFlags3_3_5 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_5 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec3_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_5

private abbrev cSpec3_3_6 := specAt3 3 6
private theorem cFlags3_3_6 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_6 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_52 coordinateInput3_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_52 hCoordinate3_53]
  decide +kernel
private abbrev cSpec3_3_7 := specAt3 3 7
private theorem cFlags3_3_7 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_7 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_54 coordinateInput3_55 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_54 hCoordinate3_55]
  decide +kernel
private abbrev cSpec3_3_8 := specAt3 3 8
private theorem cFlags3_3_8 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_8 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_56 coordinateInput3_57 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_56 hCoordinate3_57]
  decide +kernel
private abbrev cSpec3_3_9 := specAt3 3 9
private theorem cFlags3_3_9 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_9 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_58 coordinateInput3_59 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_58 hCoordinate3_59]
  decide +kernel
private abbrev cSpec3_3_10 := specAt3 3 10
private theorem cFlags3_3_10 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_10 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_60 coordinateInput3_61 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_60 hCoordinate3_61]
  decide +kernel
private abbrev cSpec3_3_11 := specAt3 3 11
private theorem cFlags3_3_11 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_11 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_62 coordinateInput3_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_62 hCoordinate3_63]
  decide +kernel
private abbrev cSpec3_3_12 := specAt3 3 12
private theorem cFlags3_3_12 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_12 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_64 coordinateInput3_65 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_64 hCoordinate3_65]
  decide +kernel
private abbrev cSpec3_3_13 := specAt3 3 13
private theorem cFlags3_3_13 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_13 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_66 coordinateInput3_67 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_66 hCoordinate3_67]
  decide +kernel
private abbrev cSpec3_3_14 := specAt3 3 14
private theorem cFlags3_3_14 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_14 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_68 coordinateInput3_69 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_68 hCoordinate3_69]
  decide +kernel
private abbrev cSpec3_3_15 := specAt3 3 15
private theorem cFlags3_3_15 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_15 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_70 coordinateInput3_71 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_70 hCoordinate3_71]
  decide +kernel
private abbrev cSpec3_3_16 := specAt3 3 16
private theorem cFlags3_3_16 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_16 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec3_2_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_2_11

private abbrev cSpec3_3_17 := specAt3 3 17
private theorem cFlags3_3_17 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec3_2_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_2_12

private abbrev cSpec3_3_18 := specAt3 3 18
private theorem cFlags3_3_18 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_18 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec3_2_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_2_13

private abbrev cSpec3_3_19 := specAt3 3 19
private theorem cFlags3_3_19 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_19 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec3_2_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_2_14

private abbrev cSpec3_3_20 := specAt3 3 20
private theorem cFlags3_3_20 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_20 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec3_2_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_2_15

private abbrev cSpec3_3_21 := specAt3 3 21
private theorem cFlags3_3_21 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_21 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_72 coordinateInput3_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_72 hCoordinate3_73]
  decide +kernel
private abbrev cSpec3_3_22 := specAt3 3 22
private theorem cFlags3_3_22 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_22 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_74 coordinateInput3_75 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_74 hCoordinate3_75]
  decide +kernel
private abbrev cSpec3_3_23 := specAt3 3 23
private theorem cFlags3_3_23 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_23 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_76 coordinateInput3_77 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_76 hCoordinate3_77]
  decide +kernel
private abbrev cSpec3_3_24 := specAt3 3 24
private theorem cFlags3_3_24 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_24 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_78 coordinateInput3_79 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_78 hCoordinate3_79]
  decide +kernel
private abbrev cSpec3_3_25 := specAt3 3 25
private theorem cFlags3_3_25 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_25 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_80 coordinateInput3_81 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_80 hCoordinate3_81]
  decide +kernel
private abbrev cSpec3_3_26 := specAt3 3 26
private theorem cFlags3_3_26 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec3_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_1_11

private abbrev cSpec3_3_27 := specAt3 3 27
private theorem cFlags3_3_27 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec3_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_1_12

private abbrev cSpec3_3_28 := specAt3 3 28
private theorem cFlags3_3_28 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec3_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_1_13

private abbrev cSpec3_3_29 := specAt3 3 29
private theorem cFlags3_3_29 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec3_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_1_14

private abbrev cSpec3_3_30 := specAt3 3 30
private theorem cFlags3_3_30 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec3_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_1_15

private abbrev cSpec3_3_31 := specAt3 3 31
private theorem cFlags3_3_31 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_31 = (List.replicate 20 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_2 coordinateInput3_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_2 hCoordinate3_53]
  decide +kernel
private abbrev cSpec3_3_32 := specAt3 3 32
private theorem cFlags3_3_32 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_32 = (List.replicate 8 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_52 coordinateInput3_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_52 hCoordinate3_1]
  decide +kernel
private abbrev cSpec3_3_33 := specAt3 3 33
private theorem cFlags3_3_33 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_33 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_52 coordinateInput3_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_52 hCoordinate3_63]
  decide +kernel
private abbrev cSpec3_3_34 := specAt3 3 34
private theorem cFlags3_3_34 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_34 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_62 coordinateInput3_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_62 hCoordinate3_53]
  decide +kernel
private abbrev cSpec3_3_35 := specAt3 3 35
private theorem cFlags3_3_35 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_35 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_62 coordinateInput3_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_62 hCoordinate3_43]
  decide +kernel
private abbrev cSpec3_3_36 := specAt3 3 36
private theorem cFlags3_3_36 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_36 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_42 coordinateInput3_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_42 hCoordinate3_63]
  decide +kernel
private abbrev cSpec3_3_37 := specAt3 3 37
private theorem cFlags3_3_37 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_37 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_42 coordinateInput3_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_42 hCoordinate3_73]
  decide +kernel
private abbrev cSpec3_3_38 := specAt3 3 38
private theorem cFlags3_3_38 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_38 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_72 coordinateInput3_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_72 hCoordinate3_43]
  decide +kernel
private abbrev cSpec3_3_39 := specAt3 3 39
private theorem cFlags3_3_39 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_39 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_72 coordinateInput3_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_72 hCoordinate3_33]
  decide +kernel
private abbrev cSpec3_3_40 := specAt3 3 40
private theorem cFlags3_3_40 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_40 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_32 coordinateInput3_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_32 hCoordinate3_73]
  decide +kernel
private abbrev cSpec3_3_41 := specAt3 3 41
private theorem cFlags3_3_41 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_41 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  exact (automaticFlags_same _ _ cSpec3_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_20

private abbrev cSpec3_3_42 := specAt3 3 42
private theorem cFlags3_3_42 : automaticFlags (trunkCatalog.states 3).context cSpec3_3_42 = (List.replicate 1 true) := by
  exact (automaticFlags_same _ _ cSpec3_1_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_1_21

private abbrev cSpec3_4_1 := specAt3 4 1
private theorem cFlags3_4_1 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_1 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec3_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_1

private abbrev cSpec3_4_2 := specAt3 4 2
private theorem cFlags3_4_2 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_2 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec3_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_2

private abbrev cSpec3_4_3 := specAt3 4 3
private theorem cFlags3_4_3 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_3 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec3_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_3

private abbrev cSpec3_4_4 := specAt3 4 4
private theorem cFlags3_4_4 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_4 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec3_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_4

private abbrev cSpec3_4_5 := specAt3 4 5
private theorem cFlags3_4_5 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_5 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec3_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_5

private abbrev cSpec3_4_6 := specAt3 4 6
private theorem cFlags3_4_6 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_6 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec3_3_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_3_6

private abbrev cSpec3_4_7 := specAt3 4 7
private theorem cFlags3_4_7 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_7 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec3_3_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_3_7

private abbrev cSpec3_4_8 := specAt3 4 8
private theorem cFlags3_4_8 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_8 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec3_3_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_3_8

private abbrev cSpec3_4_9 := specAt3 4 9
private theorem cFlags3_4_9 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_9 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec3_3_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_3_9

private abbrev cSpec3_4_10 := specAt3 4 10
private theorem cFlags3_4_10 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_10 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec3_3_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_3_10

private abbrev cSpec3_4_11 := specAt3 4 11
private theorem cFlags3_4_11 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_11 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_82 coordinateInput3_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_82 hCoordinate3_83]
  decide +kernel
private abbrev cSpec3_4_12 := specAt3 4 12
private theorem cFlags3_4_12 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_12 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_84 coordinateInput3_85 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_84 hCoordinate3_85]
  decide +kernel
private abbrev cSpec3_4_13 := specAt3 4 13
private theorem cFlags3_4_13 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_13 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_86 coordinateInput3_87 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_86 hCoordinate3_87]
  decide +kernel
private abbrev cSpec3_4_14 := specAt3 4 14
private theorem cFlags3_4_14 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_14 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_88 coordinateInput3_89 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_88 hCoordinate3_89]
  decide +kernel
private abbrev cSpec3_4_15 := specAt3 4 15
private theorem cFlags3_4_15 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_15 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_90 coordinateInput3_91 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_90 hCoordinate3_91]
  decide +kernel
private abbrev cSpec3_4_16 := specAt3 4 16
private theorem cFlags3_4_16 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_16 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec3_2_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_2_11

private abbrev cSpec3_4_17 := specAt3 4 17
private theorem cFlags3_4_17 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec3_2_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_2_12

private abbrev cSpec3_4_18 := specAt3 4 18
private theorem cFlags3_4_18 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_18 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec3_2_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_2_13

private abbrev cSpec3_4_19 := specAt3 4 19
private theorem cFlags3_4_19 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_19 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec3_2_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_2_14

private abbrev cSpec3_4_20 := specAt3 4 20
private theorem cFlags3_4_20 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_20 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec3_2_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_2_15

private abbrev cSpec3_4_21 := specAt3 4 21
private theorem cFlags3_4_21 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_21 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec3_3_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_3_21

private abbrev cSpec3_4_22 := specAt3 4 22
private theorem cFlags3_4_22 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_22 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec3_3_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_3_22

private abbrev cSpec3_4_23 := specAt3 4 23
private theorem cFlags3_4_23 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_23 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec3_3_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_3_23

private abbrev cSpec3_4_24 := specAt3 4 24
private theorem cFlags3_4_24 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_24 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec3_3_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_3_24

private abbrev cSpec3_4_25 := specAt3 4 25
private theorem cFlags3_4_25 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_25 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec3_3_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_3_25

private abbrev cSpec3_4_26 := specAt3 4 26
private theorem cFlags3_4_26 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec3_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_1_11

private abbrev cSpec3_4_27 := specAt3 4 27
private theorem cFlags3_4_27 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec3_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_1_12

private abbrev cSpec3_4_28 := specAt3 4 28
private theorem cFlags3_4_28 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec3_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_1_13

private abbrev cSpec3_4_29 := specAt3 4 29
private theorem cFlags3_4_29 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec3_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_1_14

private abbrev cSpec3_4_30 := specAt3 4 30
private theorem cFlags3_4_30 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec3_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_1_15

private abbrev cSpec3_4_31 := specAt3 4 31
private theorem cFlags3_4_31 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_31 = (List.replicate 20 true) := by
  exact (automaticFlags_same _ _ cSpec3_3_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_3_31

private abbrev cSpec3_4_32 := specAt3 4 32
private theorem cFlags3_4_32 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_32 = (List.replicate 8 false) := by
  exact (automaticFlags_same _ _ cSpec3_3_32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_3_32

private abbrev cSpec3_4_33 := specAt3 4 33
private theorem cFlags3_4_33 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_33 = (List.replicate 8 true) := by
  rw [automaticFlags_cached _ _ coordinateInput3_52 coordinateInput3_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_52 hCoordinate3_83]
  decide +kernel
private abbrev cSpec3_4_34 := specAt3 4 34
private theorem cFlags3_4_34 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_34 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_82 coordinateInput3_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_82 hCoordinate3_53]
  decide +kernel
private abbrev cSpec3_4_35 := specAt3 4 35
private theorem cFlags3_4_35 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_35 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_82 coordinateInput3_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_82 hCoordinate3_43]
  decide +kernel
private abbrev cSpec3_4_36 := specAt3 4 36
private theorem cFlags3_4_36 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_36 = (List.replicate 8 false) := by
  rw [automaticFlags_cached _ _ coordinateInput3_42 coordinateInput3_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate3_42 hCoordinate3_83]
  decide +kernel
private abbrev cSpec3_4_37 := specAt3 4 37
private theorem cFlags3_4_37 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_37 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec3_3_37 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_3_37

private abbrev cSpec3_4_38 := specAt3 4 38
private theorem cFlags3_4_38 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_38 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec3_3_38 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_3_38

private abbrev cSpec3_4_39 := specAt3 4 39
private theorem cFlags3_4_39 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_39 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec3_3_39 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_3_39

private abbrev cSpec3_4_40 := specAt3 4 40
private theorem cFlags3_4_40 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_40 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec3_3_40 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_3_40

private abbrev cSpec3_4_41 := specAt3 4 41
private theorem cFlags3_4_41 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_41 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  exact (automaticFlags_same _ _ cSpec3_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_0_20

private abbrev cSpec3_4_42 := specAt3 4 42
private theorem cFlags3_4_42 : automaticFlags (trunkCatalog.states 3).context cSpec3_4_42 = (List.replicate 1 true) := by
  exact (automaticFlags_same _ _ cSpec3_1_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags3_1_21

private theorem keys_eq : coverageKeys (trunkCatalog.states 3) = checkedKeys := by
  rfl
private theorem tasks_eq : coverageTasks (trunkCatalog.states 3) = checkedTasks := by
  rw [← coverageTasksProjection_eq]
  change [(0,[(1, (automaticFlags (trunkCatalog.states 3).context cSpec3_0_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 3).context cSpec3_0_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 3).context cSpec3_0_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 3).context cSpec3_0_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 3).context cSpec3_0_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 3).context cSpec3_0_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 3).context cSpec3_0_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 3).context cSpec3_0_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 3).context cSpec3_0_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 3).context cSpec3_0_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 3).context cSpec3_0_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 3).context cSpec3_0_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 3).context cSpec3_0_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 3).context cSpec3_0_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 3).context cSpec3_0_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 3).context cSpec3_0_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 3).context cSpec3_0_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 3).context cSpec3_0_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 3).context cSpec3_0_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 3).context cSpec3_0_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 3).context cSpec3_0_21).zipIdx.map Prod.swap)]),(1,[(1, (automaticFlags (trunkCatalog.states 3).context cSpec3_1_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 3).context cSpec3_1_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 3).context cSpec3_1_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 3).context cSpec3_1_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 3).context cSpec3_1_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 3).context cSpec3_1_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 3).context cSpec3_1_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 3).context cSpec3_1_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 3).context cSpec3_1_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 3).context cSpec3_1_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 3).context cSpec3_1_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 3).context cSpec3_1_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 3).context cSpec3_1_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 3).context cSpec3_1_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 3).context cSpec3_1_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 3).context cSpec3_1_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 3).context cSpec3_1_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 3).context cSpec3_1_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 3).context cSpec3_1_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 3).context cSpec3_1_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 3).context cSpec3_1_21).zipIdx.map Prod.swap)]),(2,[(1, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 3).context cSpec3_2_26).zipIdx.map Prod.swap)]),(3,[(1, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 3).context cSpec3_3_42).zipIdx.map Prod.swap)]),(4,[(1, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 3).context cSpec3_4_42).zipIdx.map Prod.swap)])] = checkedTasks
  rw [cFlags3_0_1, cFlags3_0_2, cFlags3_0_3, cFlags3_0_4, cFlags3_0_5, cFlags3_0_6, cFlags3_0_7, cFlags3_0_8, cFlags3_0_9, cFlags3_0_10, cFlags3_0_11, cFlags3_0_12, cFlags3_0_13, cFlags3_0_14, cFlags3_0_15, cFlags3_0_16, cFlags3_0_17, cFlags3_0_18, cFlags3_0_19, cFlags3_0_20, cFlags3_0_21, cFlags3_1_1, cFlags3_1_2, cFlags3_1_3, cFlags3_1_4, cFlags3_1_5, cFlags3_1_6, cFlags3_1_7, cFlags3_1_8, cFlags3_1_9, cFlags3_1_10, cFlags3_1_11, cFlags3_1_12, cFlags3_1_13, cFlags3_1_14, cFlags3_1_15, cFlags3_1_16, cFlags3_1_17, cFlags3_1_18, cFlags3_1_19, cFlags3_1_20, cFlags3_1_21, cFlags3_2_1, cFlags3_2_2, cFlags3_2_3, cFlags3_2_4, cFlags3_2_5, cFlags3_2_6, cFlags3_2_7, cFlags3_2_8, cFlags3_2_9, cFlags3_2_10, cFlags3_2_11, cFlags3_2_12, cFlags3_2_13, cFlags3_2_14, cFlags3_2_15, cFlags3_2_16, cFlags3_2_17, cFlags3_2_18, cFlags3_2_19, cFlags3_2_20, cFlags3_2_21, cFlags3_2_22, cFlags3_2_23, cFlags3_2_24, cFlags3_2_25, cFlags3_2_26, cFlags3_3_1, cFlags3_3_2, cFlags3_3_3, cFlags3_3_4, cFlags3_3_5, cFlags3_3_6, cFlags3_3_7, cFlags3_3_8, cFlags3_3_9, cFlags3_3_10, cFlags3_3_11, cFlags3_3_12, cFlags3_3_13, cFlags3_3_14, cFlags3_3_15, cFlags3_3_16, cFlags3_3_17, cFlags3_3_18, cFlags3_3_19, cFlags3_3_20, cFlags3_3_21, cFlags3_3_22, cFlags3_3_23, cFlags3_3_24, cFlags3_3_25, cFlags3_3_26, cFlags3_3_27, cFlags3_3_28, cFlags3_3_29, cFlags3_3_30, cFlags3_3_31, cFlags3_3_32, cFlags3_3_33, cFlags3_3_34, cFlags3_3_35, cFlags3_3_36, cFlags3_3_37, cFlags3_3_38, cFlags3_3_39, cFlags3_3_40, cFlags3_3_41, cFlags3_3_42, cFlags3_4_1, cFlags3_4_2, cFlags3_4_3, cFlags3_4_4, cFlags3_4_5, cFlags3_4_6, cFlags3_4_7, cFlags3_4_8, cFlags3_4_9, cFlags3_4_10, cFlags3_4_11, cFlags3_4_12, cFlags3_4_13, cFlags3_4_14, cFlags3_4_15, cFlags3_4_16, cFlags3_4_17, cFlags3_4_18, cFlags3_4_19, cFlags3_4_20, cFlags3_4_21, cFlags3_4_22, cFlags3_4_23, cFlags3_4_24, cFlags3_4_25, cFlags3_4_26, cFlags3_4_27, cFlags3_4_28, cFlags3_4_29, cFlags3_4_30, cFlags3_4_31, cFlags3_4_32, cFlags3_4_33, cFlags3_4_34, cFlags3_4_35, cFlags3_4_36, cFlags3_4_37, cFlags3_4_38, cFlags3_4_39, cFlags3_4_40, cFlags3_4_41, cFlags3_4_42]
  rfl
private theorem parents_length : (trunkRawParents (trunkCatalog.states 3).context).length = 100 := by
  decide +kernel
private theorem table_checked : coverageTable checkedKeys checkedTasks 100 := by
  apply coverageRemainder_sound _ _ _ [[21, 41, 53], [], [41, 53, 73, 75, 93], [73, 75, 79], [75]]
  unfold coverageRemainder parentsFor
  decide +kernel

theorem solution : trunkCoverage trunkCatalog 3 := by
  apply coverageTable_sound 3
  · unfold certRectangleValid; decide +kernel
  · decide +kernel
  · rw [keys_eq, tasks_eq, parents_length]
    exact table_checked
#print axioms solution
