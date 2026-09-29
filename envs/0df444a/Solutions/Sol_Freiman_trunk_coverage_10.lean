-- Prove2me | solution 1 for Freiman.trunk_coverage_10
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:49:28.359517+00:00
-- url     : https://prove2.me/submissions/de81cf55-3fdf-4b5b-913b-fcd6b8deb51b

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

private def coordinateFields10 : Array CertField := #[⟨(4/13),(1/13),(0/1),(0/1)⟩,⟨(52/73),(1/73),(0/1),(0/1)⟩,⟨(9/13),(-1/13),(0/1),(0/1)⟩,⟨(2/1),(-1/1),(0/1),(0/1)⟩,⟨(15/37),(-1/37),(0/1),(0/1)⟩,⟨(125/214),(-1/214),(0/1),(0/1)⟩,⟨(66/179),(-1/537),(0/1),(0/1)⟩,⟨(22/37),(1/37),(0/1),(0/1)⟩,⟨(17/22),(-1/22),(0/1),(0/1)⟩,⟨(101/143),(-1/429),(0/1),(0/1)⟩,⟨(35/94),(1/94),(0/1),(0/1)⟩,⟨(10/23),(-1/69),(0/1),(0/1)⟩,⟨(517/1249),(-1/1249),(0/1),(0/1)⟩,⟨(89/214),(1/214),(0/1),(0/1)⟩,⟨(5/22),(1/22),(0/1),(0/1)⟩,⟨(271/1006),(-1/1006),(0/1),(0/1)⟩,⟨(16/59),(1/177),(0/1),(0/1)⟩,⟨(43/142),(-1/142),(0/1),(0/1)⟩,⟨(731/2497),(-1/2497),(0/1),(0/1)⟩,⟨(42/143),(1/429),(0/1),(0/1)⟩,⟨(767/2749),(1/2749),(0/1),(0/1)⟩,⟨(1809/6094),(1/6094),(0/1),(0/1)⟩,⟨(553/1429),(1/1429),(0/1),(0/1)⟩,⟨(1272/3013),(1/3013),(0/1),(0/1)⟩,⟨(3289/10753),(1/10753),(0/1),(0/1)⟩,⟨(71/229),(-1/229),(0/1),(0/1)⟩,⟨(1413/4654),(-1/4654),(0/1),(0/1)⟩,⟨(6697/22079),(-1/66237),(0/1),(0/1)⟩,⟨(469/1549),(1/1549),(0/1),(0/1)⟩,⟨(579/1894),(-1/1894),(0/1),(0/1)⟩,⟨(9014/29557),(-1/29557),(0/1),(0/1)⟩,⟨(113/179),(1/537),(0/1),(0/1)⟩,⟨(735/1006),(1/1006),(0/1),(0/1)⟩,⟨(13/23),(1/69),(0/1),(0/1)⟩,⟨(732/1249),(1/1249),(0/1),(0/1)⟩,⟨(59/94),(-1/94),(0/1),(0/1)⟩]
private abbrev coordinateInput10_0 : LowerPair × Bool × Bool := (([2], []), true, false)
private def coordinateCodes10_0 : List (ℕ × ℕ) := [(0, 1), (0, 1)]
private abbrev coordinateInput10_1 : LowerPair × Bool × Bool := (([1], []), false, false)
private def coordinateCodes10_1 : List (ℕ × ℕ) := [(2, 3), (2, 4), (2, 3), (5, 3), (2, 3)]
private abbrev coordinateInput10_2 : LowerPair × Bool × Bool := (([1], []), true, false)
private def coordinateCodes10_2 : List (ℕ × ℕ) := [(1, 1), (1, 1)]
private abbrev coordinateInput10_3 : LowerPair × Bool × Bool := (([2], []), false, false)
private def coordinateCodes10_3 : List (ℕ × ℕ) := [(4, 3), (4, 4), (4, 3), (6, 3), (4, 3)]
private abbrev coordinateInput10_4 : LowerPair × Bool × Bool := (([1, 1], []), true, false)
private def coordinateCodes10_4 : List (ℕ × ℕ) := [(7, 1)]
private abbrev coordinateInput10_5 : LowerPair × Bool × Bool := (([1, 2], []), false, false)
private def coordinateCodes10_5 : List (ℕ × ℕ) := [(8, 3), (8, 4), (8, 3), (9, 3)]
private abbrev coordinateInput10_6 : LowerPair × Bool × Bool := (([1, 2], []), true, false)
private def coordinateCodes10_6 : List (ℕ × ℕ) := [(1, 1)]
private abbrev coordinateInput10_7 : LowerPair × Bool × Bool := (([1, 1], []), false, false)
private def coordinateCodes10_7 : List (ℕ × ℕ) := [(2, 3), (2, 4), (2, 3), (5, 3)]
private abbrev coordinateInput10_8 : LowerPair × Bool × Bool := (([1], [1]), true, true)
private def coordinateCodes10_8 : List (ℕ × ℕ) := [(1, 1)]
private abbrev coordinateInput10_9 : LowerPair × Bool × Bool := (([1], [2]), false, true)
private def coordinateCodes10_9 : List (ℕ × ℕ) := [(2, 4), (2, 6), (2, 4), (5, 4)]
private abbrev coordinateInput10_10 : LowerPair × Bool × Bool := (([1], [2]), true, true)
private def coordinateCodes10_10 : List (ℕ × ℕ) := [(1, 0)]
private abbrev coordinateInput10_11 : LowerPair × Bool × Bool := (([1], [1]), false, true)
private def coordinateCodes10_11 : List (ℕ × ℕ) := [(2, 2), (2, 5), (2, 2), (5, 2)]
private abbrev coordinateInput10_12 : LowerPair × Bool × Bool := (([2, 1], []), true, false)
private def coordinateCodes10_12 : List (ℕ × ℕ) := [(10, 1)]
private abbrev coordinateInput10_13 : LowerPair × Bool × Bool := (([2, 2], []), false, false)
private def coordinateCodes10_13 : List (ℕ × ℕ) := [(11, 3), (11, 4), (11, 3), (12, 3)]
private abbrev coordinateInput10_14 : LowerPair × Bool × Bool := (([2, 2], []), true, false)
private def coordinateCodes10_14 : List (ℕ × ℕ) := [(13, 1)]
private abbrev coordinateInput10_15 : LowerPair × Bool × Bool := (([2, 1], []), false, false)
private def coordinateCodes10_15 : List (ℕ × ℕ) := [(4, 3), (4, 4), (4, 3), (6, 3)]
private abbrev coordinateInput10_16 : LowerPair × Bool × Bool := (([2], [1]), true, true)
private def coordinateCodes10_16 : List (ℕ × ℕ) := [(0, 1)]
private abbrev coordinateInput10_17 : LowerPair × Bool × Bool := (([2], [2]), false, true)
private def coordinateCodes10_17 : List (ℕ × ℕ) := [(4, 4), (4, 6), (4, 4), (6, 4)]
private abbrev coordinateInput10_18 : LowerPair × Bool × Bool := (([2], [2]), true, true)
private def coordinateCodes10_18 : List (ℕ × ℕ) := [(0, 0), (0, 13), (0, 0), (13, 0)]
private abbrev coordinateInput10_19 : LowerPair × Bool × Bool := (([2], [1]), false, true)
private def coordinateCodes10_19 : List (ℕ × ℕ) := [(4, 2), (4, 5), (4, 2), (6, 2)]
private abbrev coordinateInput10_20 : LowerPair × Bool × Bool := (([3], []), true, false)
private def coordinateCodes10_20 : List (ℕ × ℕ) := [(14, 1), (14, 1)]
private abbrev coordinateInput10_21 : LowerPair × Bool × Bool := (([3], []), false, false)
private def coordinateCodes10_21 : List (ℕ × ℕ) := [(15, 3), (15, 3)]
private abbrev coordinateInput10_22 : LowerPair × Bool × Bool := (([3, 1], []), true, false)
private def coordinateCodes10_22 : List (ℕ × ℕ) := [(16, 1)]
private abbrev coordinateInput10_23 : LowerPair × Bool × Bool := (([3, 2], []), false, false)
private def coordinateCodes10_23 : List (ℕ × ℕ) := [(17, 3), (17, 4), (17, 3), (18, 3)]
private abbrev coordinateInput10_24 : LowerPair × Bool × Bool := (([3, 2], []), true, false)
private def coordinateCodes10_24 : List (ℕ × ℕ) := [(19, 1)]
private abbrev coordinateInput10_25 : LowerPair × Bool × Bool := (([3, 1], []), false, false)
private def coordinateCodes10_25 : List (ℕ × ℕ) := [(15, 3)]
private abbrev coordinateInput10_26 : LowerPair × Bool × Bool := (([3], [1]), true, true)
private def coordinateCodes10_26 : List (ℕ × ℕ) := [(14, 1)]
private abbrev coordinateInput10_27 : LowerPair × Bool × Bool := (([3], [2]), false, true)
private def coordinateCodes10_27 : List (ℕ × ℕ) := [(15, 4)]
private abbrev coordinateInput10_28 : LowerPair × Bool × Bool := (([3], [2]), true, true)
private def coordinateCodes10_28 : List (ℕ × ℕ) := [(14, 0), (14, 13), (14, 0), (19, 0)]
private abbrev coordinateInput10_29 : LowerPair × Bool × Bool := (([3], [1]), false, true)
private def coordinateCodes10_29 : List (ℕ × ℕ) := [(15, 2)]
private abbrev coordinateInput10_30 : LowerPair × Bool × Bool := (([], []), true, false)
private def coordinateCodes10_30 : List (ℕ × ℕ) := [(1, 1)]
private abbrev coordinateInput10_31 : LowerPair × Bool × Bool := (([], []), false, false)
private def coordinateCodes10_31 : List (ℕ × ℕ) := [(3, 3), (3, 4), (3, 3), (4, 3)]
private abbrev coordinateInput10_32 : LowerPair × Bool × Bool := (([3], [2]), true, false)
private def coordinateCodes10_32 : List (ℕ × ℕ) := [(14, 0), (14, 13), (14, 0), (19, 0)]
private abbrev coordinateInput10_33 : LowerPair × Bool × Bool := (([3], [2]), false, false)
private def coordinateCodes10_33 : List (ℕ × ℕ) := [(15, 4)]
private abbrev coordinateInput10_34 : LowerPair × Bool × Bool := (([3, 1], [2]), true, false)
private def coordinateCodes10_34 : List (ℕ × ℕ) := [(16, 0), (16, 13), (16, 0), (20, 0), (16, 0)]
private abbrev coordinateInput10_35 : LowerPair × Bool × Bool := (([3, 2], [2]), false, false)
private def coordinateCodes10_35 : List (ℕ × ℕ) := [(17, 4), (17, 4), (17, 6), (17, 4), (18, 4)]
private abbrev coordinateInput10_36 : LowerPair × Bool × Bool := (([3, 2], [2]), true, false)
private def coordinateCodes10_36 : List (ℕ × ℕ) := [(19, 0), (19, 13), (19, 0), (21, 0), (19, 0)]
private abbrev coordinateInput10_37 : LowerPair × Bool × Bool := (([3, 1], [2]), false, false)
private def coordinateCodes10_37 : List (ℕ × ℕ) := [(15, 4), (15, 4)]
private abbrev coordinateInput10_38 : LowerPair × Bool × Bool := (([3], [2, 1]), true, true)
private def coordinateCodes10_38 : List (ℕ × ℕ) := [(14, 10), (14, 10), (14, 22), (14, 10), (19, 10)]
private abbrev coordinateInput10_39 : LowerPair × Bool × Bool := (([3], [2, 2]), false, true)
private def coordinateCodes10_39 : List (ℕ × ℕ) := [(15, 11), (15, 11)]
private abbrev coordinateInput10_40 : LowerPair × Bool × Bool := (([3], [2, 2]), true, true)
private def coordinateCodes10_40 : List (ℕ × ℕ) := [(14, 13), (14, 13), (14, 23), (14, 13), (19, 13)]
private abbrev coordinateInput10_41 : LowerPair × Bool × Bool := (([3], [2, 1]), false, true)
private def coordinateCodes10_41 : List (ℕ × ℕ) := [(15, 4), (15, 4)]
private abbrev coordinateInput10_42 : LowerPair × Bool × Bool := (([3, 3], [3, 3]), true, false)
private def coordinateCodes10_42 : List (ℕ × ℕ) := [(24, 24)]
private abbrev coordinateInput10_43 : LowerPair × Bool × Bool := (([3, 3], [3, 3]), false, false)
private def coordinateCodes10_43 : List (ℕ × ℕ) := [(25, 25), (25, 26), (25, 25), (26, 25)]
private abbrev coordinateInput10_44 : LowerPair × Bool × Bool := (([3, 3, 1], [3, 3]), true, false)
private def coordinateCodes10_44 : List (ℕ × ℕ) := [(24, 24), (24, 24)]
private abbrev coordinateInput10_45 : LowerPair × Bool × Bool := (([3, 3, 2], [3, 3]), false, false)
private def coordinateCodes10_45 : List (ℕ × ℕ) := [(26, 25), (26, 26), (26, 25), (27, 25), (26, 25)]
private abbrev coordinateInput10_46 : LowerPair × Bool × Bool := (([3, 3, 2], [3, 3]), true, false)
private def coordinateCodes10_46 : List (ℕ × ℕ) := [(28, 24), (28, 24)]
private abbrev coordinateInput10_47 : LowerPair × Bool × Bool := (([3, 3, 1], [3, 3]), false, false)
private def coordinateCodes10_47 : List (ℕ × ℕ) := [(29, 25), (29, 26), (29, 25), (30, 25), (29, 25)]
private abbrev coordinateInput10_48 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 1]), true, true)
private def coordinateCodes10_48 : List (ℕ × ℕ) := [(24, 24), (24, 24)]
private abbrev coordinateInput10_49 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 2]), false, true)
private def coordinateCodes10_49 : List (ℕ × ℕ) := [(25, 26), (25, 26), (25, 27), (25, 26), (26, 26)]
private abbrev coordinateInput10_50 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 2]), true, true)
private def coordinateCodes10_50 : List (ℕ × ℕ) := [(24, 28), (24, 28)]
private abbrev coordinateInput10_51 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 1]), false, true)
private def coordinateCodes10_51 : List (ℕ × ℕ) := [(25, 29), (25, 29), (25, 30), (25, 29), (26, 29)]
private abbrev coordinateInput10_52 : LowerPair × Bool × Bool := (([3], [3]), true, false)
private def coordinateCodes10_52 : List (ℕ × ℕ) := [(14, 14), (14, 19), (14, 14), (19, 14)]
private abbrev coordinateInput10_53 : LowerPair × Bool × Bool := (([3], [3]), false, false)
private def coordinateCodes10_53 : List (ℕ × ℕ) := [(15, 15)]
private abbrev coordinateInput10_54 : LowerPair × Bool × Bool := (([3, 1], [3]), true, false)
private def coordinateCodes10_54 : List (ℕ × ℕ) := [(16, 14), (16, 19), (16, 14), (20, 14), (16, 14)]
private abbrev coordinateInput10_55 : LowerPair × Bool × Bool := (([3, 2], [3]), false, false)
private def coordinateCodes10_55 : List (ℕ × ℕ) := [(17, 15), (17, 15)]
private abbrev coordinateInput10_56 : LowerPair × Bool × Bool := (([3, 2], [3]), true, false)
private def coordinateCodes10_56 : List (ℕ × ℕ) := [(19, 14), (19, 19), (19, 14), (21, 14), (19, 14)]
private abbrev coordinateInput10_57 : LowerPair × Bool × Bool := (([3, 1], [3]), false, false)
private def coordinateCodes10_57 : List (ℕ × ℕ) := [(15, 15), (15, 15)]
private abbrev coordinateInput10_58 : LowerPair × Bool × Bool := (([3], [3, 1]), true, true)
private def coordinateCodes10_58 : List (ℕ × ℕ) := [(14, 16), (14, 16), (14, 20), (14, 16), (19, 16)]
private abbrev coordinateInput10_59 : LowerPair × Bool × Bool := (([3], [3, 2]), false, true)
private def coordinateCodes10_59 : List (ℕ × ℕ) := [(15, 17), (15, 17)]
private abbrev coordinateInput10_60 : LowerPair × Bool × Bool := (([3], [3, 2]), true, true)
private def coordinateCodes10_60 : List (ℕ × ℕ) := [(14, 19), (14, 19), (14, 21), (14, 19), (19, 19)]
private abbrev coordinateInput10_61 : LowerPair × Bool × Bool := (([3], [3, 1]), false, true)
private def coordinateCodes10_61 : List (ℕ × ℕ) := [(15, 15), (15, 15)]
private abbrev coordinateInput10_62 : LowerPair × Bool × Bool := (([2], [1]), true, false)
private def coordinateCodes10_62 : List (ℕ × ℕ) := [(0, 1)]
private abbrev coordinateInput10_63 : LowerPair × Bool × Bool := (([2], [1]), false, false)
private def coordinateCodes10_63 : List (ℕ × ℕ) := [(4, 2), (4, 5), (4, 2), (6, 2)]
private abbrev coordinateInput10_64 : LowerPair × Bool × Bool := (([2, 1], [1]), true, false)
private def coordinateCodes10_64 : List (ℕ × ℕ) := [(10, 1), (10, 1)]
private abbrev coordinateInput10_65 : LowerPair × Bool × Bool := (([2, 2], [1]), false, false)
private def coordinateCodes10_65 : List (ℕ × ℕ) := [(11, 2), (11, 2), (11, 5), (11, 2), (12, 2)]
private abbrev coordinateInput10_66 : LowerPair × Bool × Bool := (([2, 2], [1]), true, false)
private def coordinateCodes10_66 : List (ℕ × ℕ) := [(13, 1), (13, 1)]
private abbrev coordinateInput10_67 : LowerPair × Bool × Bool := (([2, 1], [1]), false, false)
private def coordinateCodes10_67 : List (ℕ × ℕ) := [(4, 2), (4, 2), (4, 5), (4, 2), (6, 2)]
private abbrev coordinateInput10_68 : LowerPair × Bool × Bool := (([2], [1, 1]), true, true)
private def coordinateCodes10_68 : List (ℕ × ℕ) := [(0, 7), (0, 7), (0, 31), (0, 7), (13, 7)]
private abbrev coordinateInput10_69 : LowerPair × Bool × Bool := (([2], [1, 2]), false, true)
private def coordinateCodes10_69 : List (ℕ × ℕ) := [(4, 8), (4, 9), (4, 8), (6, 8), (4, 8)]
private abbrev coordinateInput10_70 : LowerPair × Bool × Bool := (([2], [1, 2]), true, true)
private def coordinateCodes10_70 : List (ℕ × ℕ) := [(0, 1), (0, 1), (0, 32), (0, 1), (13, 1)]
private abbrev coordinateInput10_71 : LowerPair × Bool × Bool := (([2], [1, 1]), false, true)
private def coordinateCodes10_71 : List (ℕ × ℕ) := [(4, 2), (4, 5), (4, 2), (6, 2), (4, 2)]
private abbrev coordinateInput10_72 : LowerPair × Bool × Bool := (([3], [1]), true, false)
private def coordinateCodes10_72 : List (ℕ × ℕ) := [(14, 1)]
private abbrev coordinateInput10_73 : LowerPair × Bool × Bool := (([3], [1]), false, false)
private def coordinateCodes10_73 : List (ℕ × ℕ) := [(15, 2)]
private abbrev coordinateInput10_74 : LowerPair × Bool × Bool := (([3, 1], [1]), true, false)
private def coordinateCodes10_74 : List (ℕ × ℕ) := [(16, 1), (16, 1)]
private abbrev coordinateInput10_75 : LowerPair × Bool × Bool := (([3, 2], [1]), false, false)
private def coordinateCodes10_75 : List (ℕ × ℕ) := [(17, 2), (17, 2), (17, 5), (17, 2), (18, 2)]
private abbrev coordinateInput10_76 : LowerPair × Bool × Bool := (([3, 2], [1]), true, false)
private def coordinateCodes10_76 : List (ℕ × ℕ) := [(19, 1), (19, 1)]
private abbrev coordinateInput10_77 : LowerPair × Bool × Bool := (([3, 1], [1]), false, false)
private def coordinateCodes10_77 : List (ℕ × ℕ) := [(15, 2), (15, 2)]
private abbrev coordinateInput10_78 : LowerPair × Bool × Bool := (([3], [1, 1]), true, true)
private def coordinateCodes10_78 : List (ℕ × ℕ) := [(14, 7), (14, 7), (14, 31), (14, 7), (19, 7)]
private abbrev coordinateInput10_79 : LowerPair × Bool × Bool := (([3], [1, 2]), false, true)
private def coordinateCodes10_79 : List (ℕ × ℕ) := [(15, 8), (15, 8)]
private abbrev coordinateInput10_80 : LowerPair × Bool × Bool := (([3], [1, 2]), true, true)
private def coordinateCodes10_80 : List (ℕ × ℕ) := [(14, 1), (14, 1), (14, 32), (14, 1), (19, 1)]
private abbrev coordinateInput10_81 : LowerPair × Bool × Bool := (([3], [1, 1]), false, true)
private def coordinateCodes10_81 : List (ℕ × ℕ) := [(15, 2), (15, 2)]
private abbrev coordinateInput10_82 : LowerPair × Bool × Bool := (([2], [2]), true, false)
private def coordinateCodes10_82 : List (ℕ × ℕ) := [(0, 0), (0, 13), (0, 0), (13, 0)]
private abbrev coordinateInput10_83 : LowerPair × Bool × Bool := (([2], [2]), false, false)
private def coordinateCodes10_83 : List (ℕ × ℕ) := [(4, 4), (4, 6), (4, 4), (6, 4)]
private abbrev coordinateInput10_84 : LowerPair × Bool × Bool := (([2, 1], [2]), true, false)
private def coordinateCodes10_84 : List (ℕ × ℕ) := [(10, 0), (10, 13), (10, 0), (22, 0), (10, 0)]
private abbrev coordinateInput10_85 : LowerPair × Bool × Bool := (([2, 2], [2]), false, false)
private def coordinateCodes10_85 : List (ℕ × ℕ) := [(11, 4), (11, 4), (11, 6), (11, 4), (12, 4)]
private abbrev coordinateInput10_86 : LowerPair × Bool × Bool := (([2, 2], [2]), true, false)
private def coordinateCodes10_86 : List (ℕ × ℕ) := [(13, 0), (13, 13), (13, 0), (23, 0), (13, 0)]
private abbrev coordinateInput10_87 : LowerPair × Bool × Bool := (([2, 1], [2]), false, false)
private def coordinateCodes10_87 : List (ℕ × ℕ) := [(4, 4), (4, 4), (4, 6), (4, 4), (6, 4)]
private abbrev coordinateInput10_88 : LowerPair × Bool × Bool := (([2], [2, 1]), true, true)
private def coordinateCodes10_88 : List (ℕ × ℕ) := [(0, 10), (0, 10), (0, 22), (0, 10), (13, 10)]
private abbrev coordinateInput10_89 : LowerPair × Bool × Bool := (([2], [2, 2]), false, true)
private def coordinateCodes10_89 : List (ℕ × ℕ) := [(4, 11), (4, 12), (4, 11), (6, 11), (4, 11)]
private abbrev coordinateInput10_90 : LowerPair × Bool × Bool := (([2], [2, 2]), true, true)
private def coordinateCodes10_90 : List (ℕ × ℕ) := [(0, 13), (0, 13), (0, 23), (0, 13), (13, 13)]
private abbrev coordinateInput10_91 : LowerPair × Bool × Bool := (([2], [2, 1]), false, true)
private def coordinateCodes10_91 : List (ℕ × ℕ) := [(4, 4), (4, 6), (4, 4), (6, 4), (4, 4)]
private abbrev coordinateInput10_92 : LowerPair × Bool × Bool := (([2], [3]), true, false)
private def coordinateCodes10_92 : List (ℕ × ℕ) := [(0, 14), (0, 19), (0, 14), (13, 14)]
private abbrev coordinateInput10_93 : LowerPair × Bool × Bool := (([2], [3]), false, false)
private def coordinateCodes10_93 : List (ℕ × ℕ) := [(4, 15)]
private abbrev coordinateInput10_94 : LowerPair × Bool × Bool := (([2, 1], [3]), true, false)
private def coordinateCodes10_94 : List (ℕ × ℕ) := [(10, 14), (10, 19), (10, 14), (22, 14), (10, 14)]
private abbrev coordinateInput10_95 : LowerPair × Bool × Bool := (([2, 2], [3]), false, false)
private def coordinateCodes10_95 : List (ℕ × ℕ) := [(11, 15), (11, 15)]
private abbrev coordinateInput10_96 : LowerPair × Bool × Bool := (([2, 2], [3]), true, false)
private def coordinateCodes10_96 : List (ℕ × ℕ) := [(13, 14), (13, 19), (13, 14), (23, 14), (13, 14)]
private abbrev coordinateInput10_97 : LowerPair × Bool × Bool := (([2, 1], [3]), false, false)
private def coordinateCodes10_97 : List (ℕ × ℕ) := [(4, 15), (4, 15)]
private abbrev coordinateInput10_98 : LowerPair × Bool × Bool := (([2], [3, 1]), true, true)
private def coordinateCodes10_98 : List (ℕ × ℕ) := [(0, 16), (0, 16), (0, 20), (0, 16), (13, 16)]
private abbrev coordinateInput10_99 : LowerPair × Bool × Bool := (([2], [3, 2]), false, true)
private def coordinateCodes10_99 : List (ℕ × ℕ) := [(4, 17), (4, 18), (4, 17), (6, 17), (4, 17)]
private abbrev coordinateInput10_100 : LowerPair × Bool × Bool := (([2], [3, 2]), true, true)
private def coordinateCodes10_100 : List (ℕ × ℕ) := [(0, 19), (0, 19), (0, 21), (0, 19), (13, 19)]
private abbrev coordinateInput10_101 : LowerPair × Bool × Bool := (([2], [3, 1]), false, true)
private def coordinateCodes10_101 : List (ℕ × ℕ) := [(4, 15), (4, 15)]
private abbrev coordinateInput10_102 : LowerPair × Bool × Bool := (([3], [1, 1]), true, false)
private def coordinateCodes10_102 : List (ℕ × ℕ) := [(14, 7), (14, 7), (14, 31), (14, 7), (19, 7)]
private abbrev coordinateInput10_103 : LowerPair × Bool × Bool := (([3], [1, 1]), false, false)
private def coordinateCodes10_103 : List (ℕ × ℕ) := [(15, 2), (15, 2)]
private abbrev coordinateInput10_104 : LowerPair × Bool × Bool := (([3, 1], [1, 1]), true, false)
private def coordinateCodes10_104 : List (ℕ × ℕ) := [(16, 7), (16, 31), (16, 7), (20, 7)]
private abbrev coordinateInput10_105 : LowerPair × Bool × Bool := (([3, 2], [1, 1]), false, false)
private def coordinateCodes10_105 : List (ℕ × ℕ) := [(17, 2), (17, 5), (17, 2), (18, 2)]
private abbrev coordinateInput10_106 : LowerPair × Bool × Bool := (([3, 2], [1, 1]), true, false)
private def coordinateCodes10_106 : List (ℕ × ℕ) := [(19, 7), (19, 31), (19, 7), (21, 7)]
private abbrev coordinateInput10_107 : LowerPair × Bool × Bool := (([3, 1], [1, 1]), false, false)
private def coordinateCodes10_107 : List (ℕ × ℕ) := [(15, 2)]
private abbrev coordinateInput10_108 : LowerPair × Bool × Bool := (([3], [1, 1, 1]), true, true)
private def coordinateCodes10_108 : List (ℕ × ℕ) := [(14, 7), (14, 31), (14, 7), (19, 7)]
private abbrev coordinateInput10_109 : LowerPair × Bool × Bool := (([3], [1, 1, 2]), false, true)
private def coordinateCodes10_109 : List (ℕ × ℕ) := [(15, 5)]
private abbrev coordinateInput10_110 : LowerPair × Bool × Bool := (([3], [1, 1, 2]), true, true)
private def coordinateCodes10_110 : List (ℕ × ℕ) := [(14, 33), (14, 34), (14, 33), (19, 33)]
private abbrev coordinateInput10_111 : LowerPair × Bool × Bool := (([3], [1, 1, 1]), false, true)
private def coordinateCodes10_111 : List (ℕ × ℕ) := [(15, 35)]

private def decodeCoordinate10 (x : ℕ × ℕ) : CertField × CertField :=
  (coordinateFields10[x.1]?.getD ⟨0,0,0,0⟩,coordinateFields10[x.2]?.getD ⟨0,0,0,0⟩)

private theorem hCoordinate10_0 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_0.1 coordinateInput10_0.2.1 coordinateInput10_0.2.2).map Prod.fst = coordinateCodes10_0.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_1 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_1.1 coordinateInput10_1.2.1 coordinateInput10_1.2.2).map Prod.fst = coordinateCodes10_1.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_2 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_2.1 coordinateInput10_2.2.1 coordinateInput10_2.2.2).map Prod.fst = coordinateCodes10_2.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_3 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_3.1 coordinateInput10_3.2.1 coordinateInput10_3.2.2).map Prod.fst = coordinateCodes10_3.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_4 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_4.1 coordinateInput10_4.2.1 coordinateInput10_4.2.2).map Prod.fst = coordinateCodes10_4.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_5 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_5.1 coordinateInput10_5.2.1 coordinateInput10_5.2.2).map Prod.fst = coordinateCodes10_5.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_6 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_6.1 coordinateInput10_6.2.1 coordinateInput10_6.2.2).map Prod.fst = coordinateCodes10_6.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_7 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_7.1 coordinateInput10_7.2.1 coordinateInput10_7.2.2).map Prod.fst = coordinateCodes10_7.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_8 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_8.1 coordinateInput10_8.2.1 coordinateInput10_8.2.2).map Prod.fst = coordinateCodes10_8.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_9 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_9.1 coordinateInput10_9.2.1 coordinateInput10_9.2.2).map Prod.fst = coordinateCodes10_9.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_10 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_10.1 coordinateInput10_10.2.1 coordinateInput10_10.2.2).map Prod.fst = coordinateCodes10_10.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_11 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_11.1 coordinateInput10_11.2.1 coordinateInput10_11.2.2).map Prod.fst = coordinateCodes10_11.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_12 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_12.1 coordinateInput10_12.2.1 coordinateInput10_12.2.2).map Prod.fst = coordinateCodes10_12.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_13 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_13.1 coordinateInput10_13.2.1 coordinateInput10_13.2.2).map Prod.fst = coordinateCodes10_13.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_14 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_14.1 coordinateInput10_14.2.1 coordinateInput10_14.2.2).map Prod.fst = coordinateCodes10_14.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_15 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_15.1 coordinateInput10_15.2.1 coordinateInput10_15.2.2).map Prod.fst = coordinateCodes10_15.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_16 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_16.1 coordinateInput10_16.2.1 coordinateInput10_16.2.2).map Prod.fst = coordinateCodes10_16.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_17 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_17.1 coordinateInput10_17.2.1 coordinateInput10_17.2.2).map Prod.fst = coordinateCodes10_17.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_18 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_18.1 coordinateInput10_18.2.1 coordinateInput10_18.2.2).map Prod.fst = coordinateCodes10_18.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_19 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_19.1 coordinateInput10_19.2.1 coordinateInput10_19.2.2).map Prod.fst = coordinateCodes10_19.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_20 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_20.1 coordinateInput10_20.2.1 coordinateInput10_20.2.2).map Prod.fst = coordinateCodes10_20.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_21 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_21.1 coordinateInput10_21.2.1 coordinateInput10_21.2.2).map Prod.fst = coordinateCodes10_21.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_22 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_22.1 coordinateInput10_22.2.1 coordinateInput10_22.2.2).map Prod.fst = coordinateCodes10_22.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_23 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_23.1 coordinateInput10_23.2.1 coordinateInput10_23.2.2).map Prod.fst = coordinateCodes10_23.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_24 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_24.1 coordinateInput10_24.2.1 coordinateInput10_24.2.2).map Prod.fst = coordinateCodes10_24.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_25 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_25.1 coordinateInput10_25.2.1 coordinateInput10_25.2.2).map Prod.fst = coordinateCodes10_25.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_26 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_26.1 coordinateInput10_26.2.1 coordinateInput10_26.2.2).map Prod.fst = coordinateCodes10_26.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_27 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_27.1 coordinateInput10_27.2.1 coordinateInput10_27.2.2).map Prod.fst = coordinateCodes10_27.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_28 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_28.1 coordinateInput10_28.2.1 coordinateInput10_28.2.2).map Prod.fst = coordinateCodes10_28.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_29 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_29.1 coordinateInput10_29.2.1 coordinateInput10_29.2.2).map Prod.fst = coordinateCodes10_29.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_30 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_30.1 coordinateInput10_30.2.1 coordinateInput10_30.2.2).map Prod.fst = coordinateCodes10_30.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_31 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_31.1 coordinateInput10_31.2.1 coordinateInput10_31.2.2).map Prod.fst = coordinateCodes10_31.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_32 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_32.1 coordinateInput10_32.2.1 coordinateInput10_32.2.2).map Prod.fst = coordinateCodes10_32.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_33 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_33.1 coordinateInput10_33.2.1 coordinateInput10_33.2.2).map Prod.fst = coordinateCodes10_33.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_34 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_34.1 coordinateInput10_34.2.1 coordinateInput10_34.2.2).map Prod.fst = coordinateCodes10_34.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_35 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_35.1 coordinateInput10_35.2.1 coordinateInput10_35.2.2).map Prod.fst = coordinateCodes10_35.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_36 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_36.1 coordinateInput10_36.2.1 coordinateInput10_36.2.2).map Prod.fst = coordinateCodes10_36.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_37 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_37.1 coordinateInput10_37.2.1 coordinateInput10_37.2.2).map Prod.fst = coordinateCodes10_37.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_38 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_38.1 coordinateInput10_38.2.1 coordinateInput10_38.2.2).map Prod.fst = coordinateCodes10_38.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_39 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_39.1 coordinateInput10_39.2.1 coordinateInput10_39.2.2).map Prod.fst = coordinateCodes10_39.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_40 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_40.1 coordinateInput10_40.2.1 coordinateInput10_40.2.2).map Prod.fst = coordinateCodes10_40.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_41 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_41.1 coordinateInput10_41.2.1 coordinateInput10_41.2.2).map Prod.fst = coordinateCodes10_41.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_42 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_42.1 coordinateInput10_42.2.1 coordinateInput10_42.2.2).map Prod.fst = coordinateCodes10_42.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_43 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_43.1 coordinateInput10_43.2.1 coordinateInput10_43.2.2).map Prod.fst = coordinateCodes10_43.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_44 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_44.1 coordinateInput10_44.2.1 coordinateInput10_44.2.2).map Prod.fst = coordinateCodes10_44.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_45 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_45.1 coordinateInput10_45.2.1 coordinateInput10_45.2.2).map Prod.fst = coordinateCodes10_45.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_46 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_46.1 coordinateInput10_46.2.1 coordinateInput10_46.2.2).map Prod.fst = coordinateCodes10_46.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_47 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_47.1 coordinateInput10_47.2.1 coordinateInput10_47.2.2).map Prod.fst = coordinateCodes10_47.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_48 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_48.1 coordinateInput10_48.2.1 coordinateInput10_48.2.2).map Prod.fst = coordinateCodes10_48.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_49 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_49.1 coordinateInput10_49.2.1 coordinateInput10_49.2.2).map Prod.fst = coordinateCodes10_49.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_50 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_50.1 coordinateInput10_50.2.1 coordinateInput10_50.2.2).map Prod.fst = coordinateCodes10_50.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_51 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_51.1 coordinateInput10_51.2.1 coordinateInput10_51.2.2).map Prod.fst = coordinateCodes10_51.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_52 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_52.1 coordinateInput10_52.2.1 coordinateInput10_52.2.2).map Prod.fst = coordinateCodes10_52.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_53 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_53.1 coordinateInput10_53.2.1 coordinateInput10_53.2.2).map Prod.fst = coordinateCodes10_53.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_54 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_54.1 coordinateInput10_54.2.1 coordinateInput10_54.2.2).map Prod.fst = coordinateCodes10_54.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_55 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_55.1 coordinateInput10_55.2.1 coordinateInput10_55.2.2).map Prod.fst = coordinateCodes10_55.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_56 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_56.1 coordinateInput10_56.2.1 coordinateInput10_56.2.2).map Prod.fst = coordinateCodes10_56.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_57 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_57.1 coordinateInput10_57.2.1 coordinateInput10_57.2.2).map Prod.fst = coordinateCodes10_57.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_58 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_58.1 coordinateInput10_58.2.1 coordinateInput10_58.2.2).map Prod.fst = coordinateCodes10_58.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_59 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_59.1 coordinateInput10_59.2.1 coordinateInput10_59.2.2).map Prod.fst = coordinateCodes10_59.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_60 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_60.1 coordinateInput10_60.2.1 coordinateInput10_60.2.2).map Prod.fst = coordinateCodes10_60.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_61 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_61.1 coordinateInput10_61.2.1 coordinateInput10_61.2.2).map Prod.fst = coordinateCodes10_61.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_62 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_62.1 coordinateInput10_62.2.1 coordinateInput10_62.2.2).map Prod.fst = coordinateCodes10_62.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_63 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_63.1 coordinateInput10_63.2.1 coordinateInput10_63.2.2).map Prod.fst = coordinateCodes10_63.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_64 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_64.1 coordinateInput10_64.2.1 coordinateInput10_64.2.2).map Prod.fst = coordinateCodes10_64.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_65 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_65.1 coordinateInput10_65.2.1 coordinateInput10_65.2.2).map Prod.fst = coordinateCodes10_65.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_66 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_66.1 coordinateInput10_66.2.1 coordinateInput10_66.2.2).map Prod.fst = coordinateCodes10_66.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_67 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_67.1 coordinateInput10_67.2.1 coordinateInput10_67.2.2).map Prod.fst = coordinateCodes10_67.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_68 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_68.1 coordinateInput10_68.2.1 coordinateInput10_68.2.2).map Prod.fst = coordinateCodes10_68.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_69 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_69.1 coordinateInput10_69.2.1 coordinateInput10_69.2.2).map Prod.fst = coordinateCodes10_69.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_70 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_70.1 coordinateInput10_70.2.1 coordinateInput10_70.2.2).map Prod.fst = coordinateCodes10_70.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_71 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_71.1 coordinateInput10_71.2.1 coordinateInput10_71.2.2).map Prod.fst = coordinateCodes10_71.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_72 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_72.1 coordinateInput10_72.2.1 coordinateInput10_72.2.2).map Prod.fst = coordinateCodes10_72.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_73 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_73.1 coordinateInput10_73.2.1 coordinateInput10_73.2.2).map Prod.fst = coordinateCodes10_73.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_74 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_74.1 coordinateInput10_74.2.1 coordinateInput10_74.2.2).map Prod.fst = coordinateCodes10_74.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_75 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_75.1 coordinateInput10_75.2.1 coordinateInput10_75.2.2).map Prod.fst = coordinateCodes10_75.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_76 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_76.1 coordinateInput10_76.2.1 coordinateInput10_76.2.2).map Prod.fst = coordinateCodes10_76.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_77 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_77.1 coordinateInput10_77.2.1 coordinateInput10_77.2.2).map Prod.fst = coordinateCodes10_77.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_78 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_78.1 coordinateInput10_78.2.1 coordinateInput10_78.2.2).map Prod.fst = coordinateCodes10_78.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_79 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_79.1 coordinateInput10_79.2.1 coordinateInput10_79.2.2).map Prod.fst = coordinateCodes10_79.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_80 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_80.1 coordinateInput10_80.2.1 coordinateInput10_80.2.2).map Prod.fst = coordinateCodes10_80.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_81 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_81.1 coordinateInput10_81.2.1 coordinateInput10_81.2.2).map Prod.fst = coordinateCodes10_81.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_82 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_82.1 coordinateInput10_82.2.1 coordinateInput10_82.2.2).map Prod.fst = coordinateCodes10_82.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_83 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_83.1 coordinateInput10_83.2.1 coordinateInput10_83.2.2).map Prod.fst = coordinateCodes10_83.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_84 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_84.1 coordinateInput10_84.2.1 coordinateInput10_84.2.2).map Prod.fst = coordinateCodes10_84.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_85 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_85.1 coordinateInput10_85.2.1 coordinateInput10_85.2.2).map Prod.fst = coordinateCodes10_85.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_86 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_86.1 coordinateInput10_86.2.1 coordinateInput10_86.2.2).map Prod.fst = coordinateCodes10_86.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_87 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_87.1 coordinateInput10_87.2.1 coordinateInput10_87.2.2).map Prod.fst = coordinateCodes10_87.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_88 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_88.1 coordinateInput10_88.2.1 coordinateInput10_88.2.2).map Prod.fst = coordinateCodes10_88.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_89 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_89.1 coordinateInput10_89.2.1 coordinateInput10_89.2.2).map Prod.fst = coordinateCodes10_89.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_90 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_90.1 coordinateInput10_90.2.1 coordinateInput10_90.2.2).map Prod.fst = coordinateCodes10_90.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_91 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_91.1 coordinateInput10_91.2.1 coordinateInput10_91.2.2).map Prod.fst = coordinateCodes10_91.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_92 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_92.1 coordinateInput10_92.2.1 coordinateInput10_92.2.2).map Prod.fst = coordinateCodes10_92.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_93 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_93.1 coordinateInput10_93.2.1 coordinateInput10_93.2.2).map Prod.fst = coordinateCodes10_93.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_94 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_94.1 coordinateInput10_94.2.1 coordinateInput10_94.2.2).map Prod.fst = coordinateCodes10_94.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_95 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_95.1 coordinateInput10_95.2.1 coordinateInput10_95.2.2).map Prod.fst = coordinateCodes10_95.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_96 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_96.1 coordinateInput10_96.2.1 coordinateInput10_96.2.2).map Prod.fst = coordinateCodes10_96.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_97 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_97.1 coordinateInput10_97.2.1 coordinateInput10_97.2.2).map Prod.fst = coordinateCodes10_97.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_98 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_98.1 coordinateInput10_98.2.1 coordinateInput10_98.2.2).map Prod.fst = coordinateCodes10_98.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_99 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_99.1 coordinateInput10_99.2.1 coordinateInput10_99.2.2).map Prod.fst = coordinateCodes10_99.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_100 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_100.1 coordinateInput10_100.2.1 coordinateInput10_100.2.2).map Prod.fst = coordinateCodes10_100.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_101 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_101.1 coordinateInput10_101.2.1 coordinateInput10_101.2.2).map Prod.fst = coordinateCodes10_101.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_102 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_102.1 coordinateInput10_102.2.1 coordinateInput10_102.2.2).map Prod.fst = coordinateCodes10_102.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_103 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_103.1 coordinateInput10_103.2.1 coordinateInput10_103.2.2).map Prod.fst = coordinateCodes10_103.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_104 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_104.1 coordinateInput10_104.2.1 coordinateInput10_104.2.2).map Prod.fst = coordinateCodes10_104.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_105 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_105.1 coordinateInput10_105.2.1 coordinateInput10_105.2.2).map Prod.fst = coordinateCodes10_105.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_106 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_106.1 coordinateInput10_106.2.1 coordinateInput10_106.2.2).map Prod.fst = coordinateCodes10_106.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_107 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_107.1 coordinateInput10_107.2.1 coordinateInput10_107.2.2).map Prod.fst = coordinateCodes10_107.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_108 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_108.1 coordinateInput10_108.2.1 coordinateInput10_108.2.2).map Prod.fst = coordinateCodes10_108.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_109 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_109.1 coordinateInput10_109.2.1 coordinateInput10_109.2.2).map Prod.fst = coordinateCodes10_109.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_110 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_110.1 coordinateInput10_110.2.1 coordinateInput10_110.2.2).map Prod.fst = coordinateCodes10_110.map decodeCoordinate10 := by decide +kernel

private theorem hCoordinate10_111 :
    (trunkEndpointCases (trunkCatalog.states 10).context coordinateInput10_111.1 coordinateInput10_111.2.1 coordinateInput10_111.2.2).map Prod.fst = coordinateCodes10_111.map decodeCoordinate10 := by decide +kernel

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

private def checkedKeys : List CoverageKey := [(0,[0,20],0,[-1]),
(0,[1,21],0,[-1]),
(0,[2,54],0,[-1]),
(0,[3,23],0,[-1]),
(0,[4,9,14,19,24,29,34,39,44,49,50,51,52,53,55,56,57,58,60,61,62,63,65,66,67,68,70,71,72,73,75,76,77,78,80,81,82,83,85,86,87,88,90,91,92,93,95,96,97,98],0,[-1]),
(0,[5,6,7,8,15,16,17,18,25,26,27,28,35,36,37,38,40,41,42,43,59,69,79,89,94],0,[-1]),
(0,[10],0,[-1]),
(0,[11],0,[-1]),
(0,[12,64],0,[-1]),
(0,[13],0,[-1]),
(0,[22],0,[-1]),
(0,[30],0,[-1]),
(0,[31],0,[-1]),
(0,[32],0,[-1]),
(0,[33],0,[-1]),
(0,[45],0,[-1]),
(0,[46],0,[-1]),
(0,[47],0,[-1]),
(0,[48],0,[-1]),
(0,[74],2,[0,1,2,3]),
(0,[74],5,[0,1,2,3]),
(0,[74],7,[0,1,2,3]),
(0,[74],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[74],12,[0,1,2,3]),
(0,[74],15,[0,1,2,3]),
(0,[74],17,[0,1,2,3,4,5,6,7,8,9]),
(0,[74],19,[0,1,2,3,4,5,6,7,8,9]),
(0,[84],0,[-1]),
(0,[99],0,[-1]),
(1,[0,10,20,30,45],0,[-1]),
(1,[1,11,21,31,46],0,[-1]),
(1,[2,54],0,[-1]),
(1,[3,13,23,33,48],0,[-1]),
(1,[4,9,14,19,24,29,34,39,44,49,50,51,52,53,55,56,57,58,60,61,62,63,65,66,67,68,70,71,72,73,75,76,77,78,80,81,82,83,85,86,87,88,90,91,92,93,95,96,97,98],0,[-1]),
(1,[5,6,7,8,15,16,17,18,25,26,27,28,35,36,37,38,40,41,42,43,59,69,79,89,94],0,[-1]),
(1,[12,64],0,[-1]),
(1,[22,32,47],0,[-1]),
(1,[74],0,[-1]),
(1,[84],0,[-1]),
(1,[99],0,[-1]),
(2,[0,10,20,30],0,[-1]),
(2,[1,11,21,31],0,[-1]),
(2,[2,54],0,[-1]),
(2,[3,13,23,33],0,[-1]),
(2,[4,9,14,19,24,29,34,39,44,49,50,51,52,53,55,56,57,58,60,61,62,63,65,66,67,68,70,71,72,73,75,76,77,78,80,81,82,83,85,86,87,88,90,91,92,93,95,96,97,98],0,[-1]),
(2,[5,6,7,8,15,16,17,18,25,26,27,28,35,36,37,38,40,41,42,43,59,69,79,89,94],0,[-1]),
(2,[12,64],0,[-1]),
(2,[22,32],0,[-1]),
(2,[45],0,[-1]),
(2,[46],0,[-1]),
(2,[47],0,[-1]),
(2,[48],0,[-1]),
(2,[74],2,[0,1,2,3]),
(2,[74],5,[0,1,2,3]),
(2,[74,99],7,[0,1,2,3]),
(2,[74],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[74],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[74],14,[0,1,2,3,4,5,6,7,8,9]),
(2,[74],18,[0,1,2,3,4,5,6,7,8,9]),
(2,[74],20,[0,1,2,3,4,5,6,7,8,9]),
(2,[74],22,[0,1,2,3,4,5,6,7,8,9]),
(2,[74],24,[0,1,2,3,4,5,6,7,8,9]),
(2,[74],27,[0,1,2,3,4,5,6,7,8,9]),
(2,[74],29,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]),
(2,[74,99],30,[12,13,14,15]),
(2,[74],31,[0]),
(2,[84],0,[-1]),
(2,[99],2,[0,1,2,3]),
(2,[99],5,[0,1,2,3]),
(2,[99],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[99],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[99],14,[0,1,2,3,4,5,6,7,8,9]),
(2,[99],18,[0,1,2,3,4,5,6,7,8,9]),
(2,[99],20,[0,1,2,3,4,5,6,7,8,9]),
(2,[99],22,[0,1,2,3,4,5,6,7,8,9]),
(2,[99],24,[0,1,2,3,4,5,6,7,8,9]),
(2,[99],27,[0,1,2,3,4,5,6,7,8,9]),
(2,[99],29,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]),
(2,[99],31,[0]),
(3,[0,10,20,30,45],0,[-1]),
(3,[1,11,21,31,46],0,[-1]),
(3,[2,54],0,[-1]),
(3,[3,13,23,33,48],0,[-1]),
(3,[4,9,14,19,24,29,34,39,44,49,50,51,52,53,55,56,57,58,60,61,62,63,65,66,67,68,70,71,72,73,75,76,77,78,80,81,82,83,85,86,87,88,90,91,92,93,95,96,97,98],0,[-1]),
(3,[5,6,7,8,15,16,17,18,25,26,27,28,35,36,37,38,40,41,42,43,59,69,79,89,94],0,[-1]),
(3,[12,64],0,[-1]),
(3,[22,32,47],0,[-1]),
(3,[74],0,[-1]),
(3,[84],0,[-1]),
(3,[99],2,[0,1,2,3]),
(3,[99],5,[0,1,2,3]),
(3,[99],7,[0,1,2,3,4,5,6,7,8,9]),
(3,[99],9,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[99],12,[0,1,2,3,4,5,6,7,8,9]),
(3,[99],14,[0,1,2,3,4,5,6,7,8,9]),
(3,[99],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[99],19,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[99],22,[0,1,2,3,4,5,6,7,8,9]),
(3,[99],24,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[99],27,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[99],29,[0,1,2,3,4,5,6,7,8,9]),
(3,[99],32,[0,1,2,3,4]),
(3,[99],34,[0,1,2,3]),
(3,[99],35,[0,1,2,3]),
(3,[99],36,[0,1,2,3]),
(3,[99],38,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[99],39,[0,1,2,3]),
(3,[99],40,[0,1,2,3]),
(3,[99],42,[0,2,3]),
(4,[0,10,20,30,45],0,[-1]),
(4,[1,11,21,31,46],0,[-1]),
(4,[2,54],0,[-1]),
(4,[3,13,23,33,48],0,[-1]),
(4,[4,9,14,19,24,29,34,39,44,49,50,51,52,53,55,56,57,58,60,61,62,63,65,66,67,68,70,71,72,73,75,76,77,78,80,81,82,83,85,86,87,88,90,91,92,93,95,96,97,98],0,[-1]),
(4,[5,6,7,8,15,16,17,18,25,26,27,28,35,36,37,38,40,41,42,43,59,69,79,89,94],0,[-1]),
(4,[12,64],0,[-1]),
(4,[22,32,47],0,[-1]),
(4,[74],0,[-1]),
(4,[84],0,[-1]),
(4,[99],2,[0,1,2,3]),
(4,[99],5,[0,1,2,3]),
(4,[99],7,[0,1,2,3,4,5,6,7,8,9]),
(4,[99],9,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[99],12,[0,1,2,3,4,5,6,7,8,9]),
(4,[99],14,[0,1,2,3,4,5,6,7,8,9]),
(4,[99],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[99],19,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[99],22,[0,1,2,3,4,5,6,7,8,9]),
(4,[99],24,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[99],27,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[99],29,[0,1,2,3,4,5,6,7,8,9]),
(4,[99],33,[0,1,2,3,4,5,6,7,8,9]),
(4,[99],35,[0,1,2,3,4,5,6,7,8,9]),
(4,[99],37,[0,1,2,3,4,5,6,7,8,9]),
(4,[99],39,[0,1,2,3,4,5,6,7,8,9]),
(4,[99],42,[0,1,2,3,4]),
(4,[99],44,[0,1,2,3]),
(4,[99],45,[0,1,2,3]),
(4,[99],46,[0,1,2,3]),
(4,[99],48,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(4,[99],49,[0,1,2,3]),
(4,[99],50,[0,1,2,3]),
(4,[99],51,[12,13,14,15]),
(4,[99],52,[0]),
(5,[0,10,20,30,45],0,[-1]),
(5,[1,11,21,31,46],0,[-1]),
(5,[2,54],0,[-1]),
(5,[3,13,23,33,48],0,[-1]),
(5,[4,9,14,19,24,29,34,39,44,49,50,51,52,53,55,56,57,58,60,61,62,63,65,66,67,68,70,71,72,73,75,76,77,78,80,81,82,83,85,86,87,88,90,91,92,93,95,96,97,98],0,[-1]),
(5,[5,6,7,8,15,16,17,18,25,26,27,28,35,36,37,38,40,41,42,43,59,69,79,89,94],0,[-1]),
(5,[12,64],0,[-1]),
(5,[22,32,47],0,[-1]),
(5,[74],0,[-1]),
(5,[84],0,[-1]),
(5,[99],2,[0,1,2,3]),
(5,[99],5,[0,1,2,3]),
(5,[99],7,[0,1,2,3,4,5,6,7,8,9]),
(5,[99],9,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(5,[99],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(5,[99],15,[0,1,2,3]),
(5,[99],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(5,[99],19,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(5,[99],22,[0,1,2,3,4,5,6,7,8,9]),
(5,[99],24,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(5,[99],27,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(5,[99],29,[0,1,2,3,4,5,6,7,8,9]),
(5,[99],32,[0,1,2,3,4]),
(5,[99],34,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]),
(5,[99],35,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]),
(5,[99],36,[0,1,2,3,4,5,6,7]),
(5,[99],38,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(5,[99],39,[0,1,2,3]),
(5,[99],40,[0,1,2,3]),
(5,[99],42,[0,2,3]),
(6,[0,10,20,30,45],0,[-1]),
(6,[1,11,21,31,46],0,[-1]),
(6,[2,54],0,[-1]),
(6,[3,13,23,33,48],0,[-1]),
(6,[4,9,14,19,24,29,34,39,44,49,50,51,52,53,55,56,57,58,60,61,62,63,65,66,67,68,70,71,72,73,75,76,77,78,80,81,82,83,85,86,87,88,90,91,92,93,95,96,97,98],0,[-1]),
(6,[5,6,7,8,15,16,17,18,25,26,27,28,35,36,37,38,40,41,42,43,59,69,79,89,94],0,[-1]),
(6,[12,64],0,[-1]),
(6,[22,32,47],0,[-1]),
(6,[74],0,[-1]),
(6,[84],0,[-1]),
(6,[99],0,[-1])]
private def checkedTasks : List CoverageTask := [(0,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 4 false).zipIdx.map Prod.swap),(6, (List.replicate 10 true).zipIdx.map Prod.swap),(7, (List.replicate 4 false).zipIdx.map Prod.swap),(8, (List.replicate 4 true).zipIdx.map Prod.swap),(9, (List.replicate 4 true).zipIdx.map Prod.swap),(10, (List.replicate 16 false).zipIdx.map Prod.swap),(11, (List.replicate 4 true).zipIdx.map Prod.swap),(12, (List.replicate 4 false).zipIdx.map Prod.swap),(13, (List.replicate 1 true).zipIdx.map Prod.swap),(14, (List.replicate 1 true).zipIdx.map Prod.swap),(15, (List.replicate 4 false).zipIdx.map Prod.swap),(16, (List.replicate 10 true).zipIdx.map Prod.swap),(17, (List.replicate 10 false).zipIdx.map Prod.swap),(18, (List.replicate 4 true).zipIdx.map Prod.swap),(19, (List.replicate 10 false).zipIdx.map Prod.swap),(20, (List.replicate 2 true).zipIdx.map Prod.swap),(21, (List.replicate 8 true).zipIdx.map Prod.swap)]),(1,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 4 false).zipIdx.map Prod.swap),(6, (List.replicate 10 true).zipIdx.map Prod.swap),(7, (List.replicate 4 false).zipIdx.map Prod.swap),(8, (List.replicate 4 true).zipIdx.map Prod.swap),(9, (List.replicate 4 true).zipIdx.map Prod.swap),(10, (List.replicate 16 false).zipIdx.map Prod.swap),(11, (List.replicate 4 true).zipIdx.map Prod.swap),(12, (List.replicate 25 false).zipIdx.map Prod.swap),(13, (List.replicate 10 true).zipIdx.map Prod.swap),(14, (List.replicate 10 false).zipIdx.map Prod.swap),(15, (List.replicate 10 true).zipIdx.map Prod.swap),(16, (List.replicate 10 true).zipIdx.map Prod.swap),(17, (List.replicate 10 false).zipIdx.map Prod.swap),(18, (List.replicate 2 true).zipIdx.map Prod.swap),(19, (List.replicate 20 false).zipIdx.map Prod.swap),(20, (List.replicate 2 true).zipIdx.map Prod.swap),(21, [false, true, false, false].zipIdx.map Prod.swap)]),(2,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 4 false).zipIdx.map Prod.swap),(6, (List.replicate 10 true).zipIdx.map Prod.swap),(7, (List.replicate 4 false).zipIdx.map Prod.swap),(8, (List.replicate 4 true).zipIdx.map Prod.swap),(9, (List.replicate 4 true).zipIdx.map Prod.swap),(10, (List.replicate 16 false).zipIdx.map Prod.swap),(11, (List.replicate 4 true).zipIdx.map Prod.swap),(12, (List.replicate 25 false).zipIdx.map Prod.swap),(13, (List.replicate 10 true).zipIdx.map Prod.swap),(14, (List.replicate 10 false).zipIdx.map Prod.swap),(15, (List.replicate 10 true).zipIdx.map Prod.swap),(16, (List.replicate 4 true).zipIdx.map Prod.swap),(17, (List.replicate 10 true).zipIdx.map Prod.swap),(18, (List.replicate 10 false).zipIdx.map Prod.swap),(19, (List.replicate 10 true).zipIdx.map Prod.swap),(20, (List.replicate 10 false).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 10 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 10 true).zipIdx.map Prod.swap),(27, (List.replicate 10 false).zipIdx.map Prod.swap),(28, (List.replicate 2 true).zipIdx.map Prod.swap),(29, (List.replicate 20 false).zipIdx.map Prod.swap),(30, [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false].zipIdx.map Prod.swap),(31, (List.replicate 1 false).zipIdx.map Prod.swap),(32, (List.replicate 2 true).zipIdx.map Prod.swap),(33, (List.replicate 4 true).zipIdx.map Prod.swap)]),(3,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 4 false).zipIdx.map Prod.swap),(6, (List.replicate 4 true).zipIdx.map Prod.swap),(7, (List.replicate 10 false).zipIdx.map Prod.swap),(8, (List.replicate 10 true).zipIdx.map Prod.swap),(9, (List.replicate 25 false).zipIdx.map Prod.swap),(10, (List.replicate 25 true).zipIdx.map Prod.swap),(11, (List.replicate 1 true).zipIdx.map Prod.swap),(12, (List.replicate 10 false).zipIdx.map Prod.swap),(13, (List.replicate 4 true).zipIdx.map Prod.swap),(14, (List.replicate 10 false).zipIdx.map Prod.swap),(15, (List.replicate 10 true).zipIdx.map Prod.swap),(16, (List.replicate 16 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 25 true).zipIdx.map Prod.swap),(19, (List.replicate 25 false).zipIdx.map Prod.swap),(20, (List.replicate 25 true).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 25 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 4 true).zipIdx.map Prod.swap),(27, (List.replicate 25 false).zipIdx.map Prod.swap),(28, (List.replicate 10 true).zipIdx.map Prod.swap),(29, (List.replicate 10 false).zipIdx.map Prod.swap),(30, (List.replicate 10 true).zipIdx.map Prod.swap),(31, (List.replicate 8 true).zipIdx.map Prod.swap),(32, (List.replicate 5 false).zipIdx.map Prod.swap),(33, (List.replicate 1 true).zipIdx.map Prod.swap),(34, (List.replicate 4 false).zipIdx.map Prod.swap),(35, (List.replicate 4 false).zipIdx.map Prod.swap),(36, (List.replicate 4 false).zipIdx.map Prod.swap),(37, (List.replicate 4 true).zipIdx.map Prod.swap),(38, (List.replicate 16 false).zipIdx.map Prod.swap),(39, (List.replicate 4 false).zipIdx.map Prod.swap),(40, (List.replicate 4 false).zipIdx.map Prod.swap),(41, (List.replicate 2 true).zipIdx.map Prod.swap),(42, [false, true, false, false].zipIdx.map Prod.swap)]),(4,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 4 false).zipIdx.map Prod.swap),(6, (List.replicate 4 true).zipIdx.map Prod.swap),(7, (List.replicate 10 false).zipIdx.map Prod.swap),(8, (List.replicate 10 true).zipIdx.map Prod.swap),(9, (List.replicate 25 false).zipIdx.map Prod.swap),(10, (List.replicate 25 true).zipIdx.map Prod.swap),(11, (List.replicate 1 true).zipIdx.map Prod.swap),(12, (List.replicate 10 false).zipIdx.map Prod.swap),(13, (List.replicate 4 true).zipIdx.map Prod.swap),(14, (List.replicate 10 false).zipIdx.map Prod.swap),(15, (List.replicate 10 true).zipIdx.map Prod.swap),(16, (List.replicate 16 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 25 true).zipIdx.map Prod.swap),(19, (List.replicate 25 false).zipIdx.map Prod.swap),(20, (List.replicate 25 true).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 25 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 4 true).zipIdx.map Prod.swap),(27, (List.replicate 25 false).zipIdx.map Prod.swap),(28, (List.replicate 10 true).zipIdx.map Prod.swap),(29, (List.replicate 10 false).zipIdx.map Prod.swap),(30, (List.replicate 10 true).zipIdx.map Prod.swap),(31, (List.replicate 4 true).zipIdx.map Prod.swap),(32, (List.replicate 10 true).zipIdx.map Prod.swap),(33, (List.replicate 10 false).zipIdx.map Prod.swap),(34, (List.replicate 10 true).zipIdx.map Prod.swap),(35, (List.replicate 10 false).zipIdx.map Prod.swap),(36, (List.replicate 4 true).zipIdx.map Prod.swap),(37, (List.replicate 10 false).zipIdx.map Prod.swap),(38, (List.replicate 10 true).zipIdx.map Prod.swap),(39, (List.replicate 10 false).zipIdx.map Prod.swap),(40, (List.replicate 10 true).zipIdx.map Prod.swap),(41, (List.replicate 8 true).zipIdx.map Prod.swap),(42, (List.replicate 5 false).zipIdx.map Prod.swap),(43, (List.replicate 1 true).zipIdx.map Prod.swap),(44, (List.replicate 4 false).zipIdx.map Prod.swap),(45, (List.replicate 4 false).zipIdx.map Prod.swap),(46, (List.replicate 4 false).zipIdx.map Prod.swap),(47, (List.replicate 4 true).zipIdx.map Prod.swap),(48, (List.replicate 16 false).zipIdx.map Prod.swap),(49, (List.replicate 4 false).zipIdx.map Prod.swap),(50, (List.replicate 4 false).zipIdx.map Prod.swap),(51, [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false].zipIdx.map Prod.swap),(52, (List.replicate 1 false).zipIdx.map Prod.swap),(53, (List.replicate 2 true).zipIdx.map Prod.swap),(54, (List.replicate 4 true).zipIdx.map Prod.swap)]),(5,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 4 false).zipIdx.map Prod.swap),(6, (List.replicate 4 true).zipIdx.map Prod.swap),(7, (List.replicate 10 false).zipIdx.map Prod.swap),(8, (List.replicate 10 true).zipIdx.map Prod.swap),(9, (List.replicate 25 false).zipIdx.map Prod.swap),(10, (List.replicate 25 true).zipIdx.map Prod.swap),(11, (List.replicate 10 true).zipIdx.map Prod.swap),(12, (List.replicate 16 false).zipIdx.map Prod.swap),(13, (List.replicate 4 true).zipIdx.map Prod.swap),(14, (List.replicate 4 true).zipIdx.map Prod.swap),(15, (List.replicate 4 false).zipIdx.map Prod.swap),(16, (List.replicate 16 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 25 true).zipIdx.map Prod.swap),(19, (List.replicate 25 false).zipIdx.map Prod.swap),(20, (List.replicate 25 true).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 25 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 4 true).zipIdx.map Prod.swap),(27, (List.replicate 25 false).zipIdx.map Prod.swap),(28, (List.replicate 10 true).zipIdx.map Prod.swap),(29, (List.replicate 10 false).zipIdx.map Prod.swap),(30, (List.replicate 10 true).zipIdx.map Prod.swap),(31, (List.replicate 8 true).zipIdx.map Prod.swap),(32, (List.replicate 5 false).zipIdx.map Prod.swap),(33, (List.replicate 2 true).zipIdx.map Prod.swap),(34, (List.replicate 20 false).zipIdx.map Prod.swap),(35, (List.replicate 20 false).zipIdx.map Prod.swap),(36, (List.replicate 8 false).zipIdx.map Prod.swap),(37, (List.replicate 4 true).zipIdx.map Prod.swap),(38, (List.replicate 16 false).zipIdx.map Prod.swap),(39, (List.replicate 4 false).zipIdx.map Prod.swap),(40, (List.replicate 4 false).zipIdx.map Prod.swap),(41, (List.replicate 2 true).zipIdx.map Prod.swap),(42, [false, true, false, false].zipIdx.map Prod.swap)]),(6,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 4 false).zipIdx.map Prod.swap),(6, (List.replicate 4 true).zipIdx.map Prod.swap),(7, (List.replicate 10 false).zipIdx.map Prod.swap),(8, (List.replicate 10 true).zipIdx.map Prod.swap),(9, (List.replicate 25 false).zipIdx.map Prod.swap),(10, (List.replicate 25 true).zipIdx.map Prod.swap),(11, (List.replicate 10 true).zipIdx.map Prod.swap),(12, (List.replicate 16 false).zipIdx.map Prod.swap),(13, (List.replicate 4 true).zipIdx.map Prod.swap),(14, (List.replicate 4 true).zipIdx.map Prod.swap),(15, (List.replicate 4 false).zipIdx.map Prod.swap),(16, (List.replicate 16 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 25 true).zipIdx.map Prod.swap),(19, (List.replicate 25 false).zipIdx.map Prod.swap),(20, (List.replicate 25 true).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 25 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 4 true).zipIdx.map Prod.swap),(27, (List.replicate 25 false).zipIdx.map Prod.swap),(28, (List.replicate 10 true).zipIdx.map Prod.swap),(29, (List.replicate 10 false).zipIdx.map Prod.swap),(30, (List.replicate 10 true).zipIdx.map Prod.swap),(31, (List.replicate 4 true).zipIdx.map Prod.swap),(32, (List.replicate 10 true).zipIdx.map Prod.swap),(33, (List.replicate 10 false).zipIdx.map Prod.swap),(34, (List.replicate 10 true).zipIdx.map Prod.swap),(35, (List.replicate 10 false).zipIdx.map Prod.swap),(36, (List.replicate 4 true).zipIdx.map Prod.swap),(37, (List.replicate 10 false).zipIdx.map Prod.swap),(38, (List.replicate 10 true).zipIdx.map Prod.swap),(39, (List.replicate 10 false).zipIdx.map Prod.swap),(40, (List.replicate 10 true).zipIdx.map Prod.swap),(41, (List.replicate 8 true).zipIdx.map Prod.swap),(42, (List.replicate 5 false).zipIdx.map Prod.swap),(43, (List.replicate 2 true).zipIdx.map Prod.swap),(44, (List.replicate 20 false).zipIdx.map Prod.swap),(45, (List.replicate 20 false).zipIdx.map Prod.swap),(46, (List.replicate 8 false).zipIdx.map Prod.swap),(47, (List.replicate 4 true).zipIdx.map Prod.swap),(48, (List.replicate 16 false).zipIdx.map Prod.swap),(49, (List.replicate 4 false).zipIdx.map Prod.swap),(50, (List.replicate 4 false).zipIdx.map Prod.swap),(51, [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false].zipIdx.map Prod.swap),(52, (List.replicate 1 false).zipIdx.map Prod.swap),(53, (List.replicate 2 true).zipIdx.map Prod.swap),(54, (List.replicate 4 true).zipIdx.map Prod.swap)])]
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
private abbrev specAt10 (pi goal : ℕ) : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 10) pi))[goal-1]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private abbrev cSpec10_0_1 := specAt10 0 1
private theorem cFlags10_0_1 : automaticFlags (trunkCatalog.states 10).context cSpec10_0_1 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_2 coordinateInput10_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_2 hCoordinate10_1]
  decide +kernel
private abbrev cSpec10_0_2 := specAt10 0 2
private theorem cFlags10_0_2 : automaticFlags (trunkCatalog.states 10).context cSpec10_0_2 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_4 coordinateInput10_5 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_4 hCoordinate10_5]
  decide +kernel
private abbrev cSpec10_0_3 := specAt10 0 3
private theorem cFlags10_0_3 : automaticFlags (trunkCatalog.states 10).context cSpec10_0_3 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_6 coordinateInput10_7 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_6 hCoordinate10_7]
  decide +kernel
private abbrev cSpec10_0_4 := specAt10 0 4
private theorem cFlags10_0_4 : automaticFlags (trunkCatalog.states 10).context cSpec10_0_4 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_8 coordinateInput10_9 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_8 hCoordinate10_9]
  decide +kernel
private abbrev cSpec10_0_5 := specAt10 0 5
private theorem cFlags10_0_5 : automaticFlags (trunkCatalog.states 10).context cSpec10_0_5 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_10 coordinateInput10_11 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_10 hCoordinate10_11]
  decide +kernel
private abbrev cSpec10_0_6 := specAt10 0 6
private theorem cFlags10_0_6 : automaticFlags (trunkCatalog.states 10).context cSpec10_0_6 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_0 coordinateInput10_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_0 hCoordinate10_3]
  decide +kernel
private abbrev cSpec10_0_7 := specAt10 0 7
private theorem cFlags10_0_7 : automaticFlags (trunkCatalog.states 10).context cSpec10_0_7 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_12 coordinateInput10_13 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_12 hCoordinate10_13]
  decide +kernel
private abbrev cSpec10_0_8 := specAt10 0 8
private theorem cFlags10_0_8 : automaticFlags (trunkCatalog.states 10).context cSpec10_0_8 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_14 coordinateInput10_15 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_14 hCoordinate10_15]
  decide +kernel
private abbrev cSpec10_0_9 := specAt10 0 9
private theorem cFlags10_0_9 : automaticFlags (trunkCatalog.states 10).context cSpec10_0_9 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_16 coordinateInput10_17 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_16 hCoordinate10_17]
  decide +kernel
private abbrev cSpec10_0_10 := specAt10 0 10
private theorem cFlags10_0_10 : automaticFlags (trunkCatalog.states 10).context cSpec10_0_10 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_18 coordinateInput10_19 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_18 hCoordinate10_19]
  decide +kernel
private abbrev cSpec10_0_11 := specAt10 0 11
private theorem cFlags10_0_11 : automaticFlags (trunkCatalog.states 10).context cSpec10_0_11 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_20 coordinateInput10_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_20 hCoordinate10_21]
  decide +kernel
private abbrev cSpec10_0_12 := specAt10 0 12
private theorem cFlags10_0_12 : automaticFlags (trunkCatalog.states 10).context cSpec10_0_12 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_22 coordinateInput10_23 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_22 hCoordinate10_23]
  decide +kernel
private abbrev cSpec10_0_13 := specAt10 0 13
private theorem cFlags10_0_13 : automaticFlags (trunkCatalog.states 10).context cSpec10_0_13 = (List.replicate 1 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_24 coordinateInput10_25 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_24 hCoordinate10_25]
  decide +kernel
private abbrev cSpec10_0_14 := specAt10 0 14
private theorem cFlags10_0_14 : automaticFlags (trunkCatalog.states 10).context cSpec10_0_14 = (List.replicate 1 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_26 coordinateInput10_27 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_26 hCoordinate10_27]
  decide +kernel
private abbrev cSpec10_0_15 := specAt10 0 15
private theorem cFlags10_0_15 : automaticFlags (trunkCatalog.states 10).context cSpec10_0_15 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_28 coordinateInput10_29 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_28 hCoordinate10_29]
  decide +kernel
private abbrev cSpec10_0_16 := specAt10 0 16
private theorem cFlags10_0_16 : automaticFlags (trunkCatalog.states 10).context cSpec10_0_16 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_2 coordinateInput10_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_2 hCoordinate10_3]
  decide +kernel
private abbrev cSpec10_0_17 := specAt10 0 17
private theorem cFlags10_0_17 : automaticFlags (trunkCatalog.states 10).context cSpec10_0_17 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_0 coordinateInput10_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_0 hCoordinate10_1]
  decide +kernel
private abbrev cSpec10_0_18 := specAt10 0 18
private theorem cFlags10_0_18 : automaticFlags (trunkCatalog.states 10).context cSpec10_0_18 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_0 coordinateInput10_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_0 hCoordinate10_21]
  decide +kernel
private abbrev cSpec10_0_19 := specAt10 0 19
private theorem cFlags10_0_19 : automaticFlags (trunkCatalog.states 10).context cSpec10_0_19 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_20 coordinateInput10_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_20 hCoordinate10_3]
  decide +kernel
private abbrev cSpec10_0_20 := specAt10 0 20
private theorem cFlags10_0_20 : automaticFlags (trunkCatalog.states 10).context cSpec10_0_20 = (List.replicate 2 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_2 coordinateInput10_30 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_2 hCoordinate10_30]
  decide +kernel
private abbrev cSpec10_0_21 := specAt10 0 21
private theorem cFlags10_0_21 : automaticFlags (trunkCatalog.states 10).context cSpec10_0_21 = (List.replicate 8 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_31 coordinateInput10_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_31 hCoordinate10_21]
  decide +kernel
private abbrev cSpec10_1_1 := specAt10 1 1
private theorem cFlags10_1_1 : automaticFlags (trunkCatalog.states 10).context cSpec10_1_1 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_1

private abbrev cSpec10_1_2 := specAt10 1 2
private theorem cFlags10_1_2 : automaticFlags (trunkCatalog.states 10).context cSpec10_1_2 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_2

private abbrev cSpec10_1_3 := specAt10 1 3
private theorem cFlags10_1_3 : automaticFlags (trunkCatalog.states 10).context cSpec10_1_3 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_3

private abbrev cSpec10_1_4 := specAt10 1 4
private theorem cFlags10_1_4 : automaticFlags (trunkCatalog.states 10).context cSpec10_1_4 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_4

private abbrev cSpec10_1_5 := specAt10 1 5
private theorem cFlags10_1_5 : automaticFlags (trunkCatalog.states 10).context cSpec10_1_5 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_5

private abbrev cSpec10_1_6 := specAt10 1 6
private theorem cFlags10_1_6 : automaticFlags (trunkCatalog.states 10).context cSpec10_1_6 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_6

private abbrev cSpec10_1_7 := specAt10 1 7
private theorem cFlags10_1_7 : automaticFlags (trunkCatalog.states 10).context cSpec10_1_7 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_0_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_7

private abbrev cSpec10_1_8 := specAt10 1 8
private theorem cFlags10_1_8 : automaticFlags (trunkCatalog.states 10).context cSpec10_1_8 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_8

private abbrev cSpec10_1_9 := specAt10 1 9
private theorem cFlags10_1_9 : automaticFlags (trunkCatalog.states 10).context cSpec10_1_9 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_9

private abbrev cSpec10_1_10 := specAt10 1 10
private theorem cFlags10_1_10 : automaticFlags (trunkCatalog.states 10).context cSpec10_1_10 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec10_0_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_10

private abbrev cSpec10_1_11 := specAt10 1 11
private theorem cFlags10_1_11 : automaticFlags (trunkCatalog.states 10).context cSpec10_1_11 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_32 coordinateInput10_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_32 hCoordinate10_33]
  decide +kernel
private abbrev cSpec10_1_12 := specAt10 1 12
private theorem cFlags10_1_12 : automaticFlags (trunkCatalog.states 10).context cSpec10_1_12 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_34 coordinateInput10_35 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_34 hCoordinate10_35]
  decide +kernel
private abbrev cSpec10_1_13 := specAt10 1 13
private theorem cFlags10_1_13 : automaticFlags (trunkCatalog.states 10).context cSpec10_1_13 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_36 coordinateInput10_37 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_36 hCoordinate10_37]
  decide +kernel
private abbrev cSpec10_1_14 := specAt10 1 14
private theorem cFlags10_1_14 : automaticFlags (trunkCatalog.states 10).context cSpec10_1_14 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_38 coordinateInput10_39 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_38 hCoordinate10_39]
  decide +kernel
private abbrev cSpec10_1_15 := specAt10 1 15
private theorem cFlags10_1_15 : automaticFlags (trunkCatalog.states 10).context cSpec10_1_15 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_40 coordinateInput10_41 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_40 hCoordinate10_41]
  decide +kernel
private abbrev cSpec10_1_16 := specAt10 1 16
private theorem cFlags10_1_16 : automaticFlags (trunkCatalog.states 10).context cSpec10_1_16 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_16

private abbrev cSpec10_1_17 := specAt10 1 17
private theorem cFlags10_1_17 : automaticFlags (trunkCatalog.states 10).context cSpec10_1_17 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_0_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_17

private abbrev cSpec10_1_18 := specAt10 1 18
private theorem cFlags10_1_18 : automaticFlags (trunkCatalog.states 10).context cSpec10_1_18 = (List.replicate 2 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_0 coordinateInput10_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_0 hCoordinate10_33]
  decide +kernel
private abbrev cSpec10_1_19 := specAt10 1 19
private theorem cFlags10_1_19 : automaticFlags (trunkCatalog.states 10).context cSpec10_1_19 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_32 coordinateInput10_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_32 hCoordinate10_3]
  decide +kernel
private abbrev cSpec10_1_20 := specAt10 1 20
private theorem cFlags10_1_20 : automaticFlags (trunkCatalog.states 10).context cSpec10_1_20 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_20

private abbrev cSpec10_1_21 := specAt10 1 21
private theorem cFlags10_1_21 : automaticFlags (trunkCatalog.states 10).context cSpec10_1_21 = [false, true, false, false] := by
  rw [automaticFlags_cached _ _ coordinateInput10_31 coordinateInput10_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_31 hCoordinate10_33]
  decide +kernel
private abbrev cSpec10_2_1 := specAt10 2 1
private theorem cFlags10_2_1 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_1 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_1

private abbrev cSpec10_2_2 := specAt10 2 2
private theorem cFlags10_2_2 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_2 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_2

private abbrev cSpec10_2_3 := specAt10 2 3
private theorem cFlags10_2_3 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_3 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_3

private abbrev cSpec10_2_4 := specAt10 2 4
private theorem cFlags10_2_4 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_4 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_4

private abbrev cSpec10_2_5 := specAt10 2 5
private theorem cFlags10_2_5 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_5 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_5

private abbrev cSpec10_2_6 := specAt10 2 6
private theorem cFlags10_2_6 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_6 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_6

private abbrev cSpec10_2_7 := specAt10 2 7
private theorem cFlags10_2_7 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_7 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_0_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_7

private abbrev cSpec10_2_8 := specAt10 2 8
private theorem cFlags10_2_8 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_8 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_8

private abbrev cSpec10_2_9 := specAt10 2 9
private theorem cFlags10_2_9 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_9 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_9

private abbrev cSpec10_2_10 := specAt10 2 10
private theorem cFlags10_2_10 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_10 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec10_0_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_10

private abbrev cSpec10_2_11 := specAt10 2 11
private theorem cFlags10_2_11 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_11 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_11

private abbrev cSpec10_2_12 := specAt10 2 12
private theorem cFlags10_2_12 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_12 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec10_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_12

private abbrev cSpec10_2_13 := specAt10 2 13
private theorem cFlags10_2_13 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_13 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_13

private abbrev cSpec10_2_14 := specAt10 2 14
private theorem cFlags10_2_14 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_14 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_14

private abbrev cSpec10_2_15 := specAt10 2 15
private theorem cFlags10_2_15 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_15 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_15

private abbrev cSpec10_2_16 := specAt10 2 16
private theorem cFlags10_2_16 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_16 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_42 coordinateInput10_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_42 hCoordinate10_43]
  decide +kernel
private abbrev cSpec10_2_17 := specAt10 2 17
private theorem cFlags10_2_17 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_17 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_44 coordinateInput10_45 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_44 hCoordinate10_45]
  decide +kernel
private abbrev cSpec10_2_18 := specAt10 2 18
private theorem cFlags10_2_18 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_18 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_46 coordinateInput10_47 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_46 hCoordinate10_47]
  decide +kernel
private abbrev cSpec10_2_19 := specAt10 2 19
private theorem cFlags10_2_19 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_19 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_48 coordinateInput10_49 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_48 hCoordinate10_49]
  decide +kernel
private abbrev cSpec10_2_20 := specAt10 2 20
private theorem cFlags10_2_20 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_20 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_50 coordinateInput10_51 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_50 hCoordinate10_51]
  decide +kernel
private abbrev cSpec10_2_21 := specAt10 2 21
private theorem cFlags10_2_21 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_21 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_52 coordinateInput10_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_52 hCoordinate10_53]
  decide +kernel
private abbrev cSpec10_2_22 := specAt10 2 22
private theorem cFlags10_2_22 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_22 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_54 coordinateInput10_55 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_54 hCoordinate10_55]
  decide +kernel
private abbrev cSpec10_2_23 := specAt10 2 23
private theorem cFlags10_2_23 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_23 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_56 coordinateInput10_57 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_56 hCoordinate10_57]
  decide +kernel
private abbrev cSpec10_2_24 := specAt10 2 24
private theorem cFlags10_2_24 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_24 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_58 coordinateInput10_59 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_58 hCoordinate10_59]
  decide +kernel
private abbrev cSpec10_2_25 := specAt10 2 25
private theorem cFlags10_2_25 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_25 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_60 coordinateInput10_61 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_60 hCoordinate10_61]
  decide +kernel
private abbrev cSpec10_2_26 := specAt10 2 26
private theorem cFlags10_2_26 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_26 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_16

private abbrev cSpec10_2_27 := specAt10 2 27
private theorem cFlags10_2_27 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_27 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_0_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_17

private abbrev cSpec10_2_28 := specAt10 2 28
private theorem cFlags10_2_28 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_28 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec10_1_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_18

private abbrev cSpec10_2_29 := specAt10 2 29
private theorem cFlags10_2_29 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_29 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec10_1_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_19

private abbrev cSpec10_2_30 := specAt10 2 30
private theorem cFlags10_2_30 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_30 = [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false] := by
  rw [automaticFlags_cached _ _ coordinateInput10_32 coordinateInput10_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_32 hCoordinate10_43]
  decide +kernel
private abbrev cSpec10_2_31 := specAt10 2 31
private theorem cFlags10_2_31 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_31 = (List.replicate 1 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_42 coordinateInput10_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_42 hCoordinate10_33]
  decide +kernel
private abbrev cSpec10_2_32 := specAt10 2 32
private theorem cFlags10_2_32 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_32 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_20

private abbrev cSpec10_2_33 := specAt10 2 33
private theorem cFlags10_2_33 : automaticFlags (trunkCatalog.states 10).context cSpec10_2_33 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_31 coordinateInput10_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_31 hCoordinate10_53]
  decide +kernel
private abbrev cSpec10_3_1 := specAt10 3 1
private theorem cFlags10_3_1 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_1 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_1

private abbrev cSpec10_3_2 := specAt10 3 2
private theorem cFlags10_3_2 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_2 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_2

private abbrev cSpec10_3_3 := specAt10 3 3
private theorem cFlags10_3_3 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_3 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_3

private abbrev cSpec10_3_4 := specAt10 3 4
private theorem cFlags10_3_4 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_4 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_4

private abbrev cSpec10_3_5 := specAt10 3 5
private theorem cFlags10_3_5 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_5 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_5

private abbrev cSpec10_3_6 := specAt10 3 6
private theorem cFlags10_3_6 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_6 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_62 coordinateInput10_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_62 hCoordinate10_63]
  decide +kernel
private abbrev cSpec10_3_7 := specAt10 3 7
private theorem cFlags10_3_7 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_7 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_64 coordinateInput10_65 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_64 hCoordinate10_65]
  decide +kernel
private abbrev cSpec10_3_8 := specAt10 3 8
private theorem cFlags10_3_8 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_8 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_66 coordinateInput10_67 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_66 hCoordinate10_67]
  decide +kernel
private abbrev cSpec10_3_9 := specAt10 3 9
private theorem cFlags10_3_9 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_9 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_68 coordinateInput10_69 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_68 hCoordinate10_69]
  decide +kernel
private abbrev cSpec10_3_10 := specAt10 3 10
private theorem cFlags10_3_10 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_10 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_70 coordinateInput10_71 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_70 hCoordinate10_71]
  decide +kernel
private abbrev cSpec10_3_11 := specAt10 3 11
private theorem cFlags10_3_11 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_11 = (List.replicate 1 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_72 coordinateInput10_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_72 hCoordinate10_73]
  decide +kernel
private abbrev cSpec10_3_12 := specAt10 3 12
private theorem cFlags10_3_12 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_12 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_74 coordinateInput10_75 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_74 hCoordinate10_75]
  decide +kernel
private abbrev cSpec10_3_13 := specAt10 3 13
private theorem cFlags10_3_13 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_13 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_76 coordinateInput10_77 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_76 hCoordinate10_77]
  decide +kernel
private abbrev cSpec10_3_14 := specAt10 3 14
private theorem cFlags10_3_14 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_14 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_78 coordinateInput10_79 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_78 hCoordinate10_79]
  decide +kernel
private abbrev cSpec10_3_15 := specAt10 3 15
private theorem cFlags10_3_15 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_15 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_80 coordinateInput10_81 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_80 hCoordinate10_81]
  decide +kernel
private abbrev cSpec10_3_16 := specAt10 3 16
private theorem cFlags10_3_16 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_16 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_82 coordinateInput10_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_82 hCoordinate10_83]
  decide +kernel
private abbrev cSpec10_3_17 := specAt10 3 17
private theorem cFlags10_3_17 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_17 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_84 coordinateInput10_85 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_84 hCoordinate10_85]
  decide +kernel
private abbrev cSpec10_3_18 := specAt10 3 18
private theorem cFlags10_3_18 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_18 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_86 coordinateInput10_87 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_86 hCoordinate10_87]
  decide +kernel
private abbrev cSpec10_3_19 := specAt10 3 19
private theorem cFlags10_3_19 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_19 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_88 coordinateInput10_89 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_88 hCoordinate10_89]
  decide +kernel
private abbrev cSpec10_3_20 := specAt10 3 20
private theorem cFlags10_3_20 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_20 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_90 coordinateInput10_91 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_90 hCoordinate10_91]
  decide +kernel
private abbrev cSpec10_3_21 := specAt10 3 21
private theorem cFlags10_3_21 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_21 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_92 coordinateInput10_93 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_92 hCoordinate10_93]
  decide +kernel
private abbrev cSpec10_3_22 := specAt10 3 22
private theorem cFlags10_3_22 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_22 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_94 coordinateInput10_95 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_94 hCoordinate10_95]
  decide +kernel
private abbrev cSpec10_3_23 := specAt10 3 23
private theorem cFlags10_3_23 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_23 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_96 coordinateInput10_97 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_96 hCoordinate10_97]
  decide +kernel
private abbrev cSpec10_3_24 := specAt10 3 24
private theorem cFlags10_3_24 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_24 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_98 coordinateInput10_99 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_98 hCoordinate10_99]
  decide +kernel
private abbrev cSpec10_3_25 := specAt10 3 25
private theorem cFlags10_3_25 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_25 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_100 coordinateInput10_101 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_100 hCoordinate10_101]
  decide +kernel
private abbrev cSpec10_3_26 := specAt10 3 26
private theorem cFlags10_3_26 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_11

private abbrev cSpec10_3_27 := specAt10 3 27
private theorem cFlags10_3_27 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec10_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_12

private abbrev cSpec10_3_28 := specAt10 3 28
private theorem cFlags10_3_28 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_13

private abbrev cSpec10_3_29 := specAt10 3 29
private theorem cFlags10_3_29 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_14

private abbrev cSpec10_3_30 := specAt10 3 30
private theorem cFlags10_3_30 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_15

private abbrev cSpec10_3_31 := specAt10 3 31
private theorem cFlags10_3_31 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_31 = (List.replicate 8 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_2 coordinateInput10_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_2 hCoordinate10_63]
  decide +kernel
private abbrev cSpec10_3_32 := specAt10 3 32
private theorem cFlags10_3_32 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_32 = (List.replicate 5 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_62 coordinateInput10_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_62 hCoordinate10_1]
  decide +kernel
private abbrev cSpec10_3_33 := specAt10 3 33
private theorem cFlags10_3_33 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_33 = (List.replicate 1 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_62 coordinateInput10_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_62 hCoordinate10_73]
  decide +kernel
private abbrev cSpec10_3_34 := specAt10 3 34
private theorem cFlags10_3_34 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_34 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_72 coordinateInput10_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_72 hCoordinate10_63]
  decide +kernel
private abbrev cSpec10_3_35 := specAt10 3 35
private theorem cFlags10_3_35 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_35 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_72 coordinateInput10_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_72 hCoordinate10_83]
  decide +kernel
private abbrev cSpec10_3_36 := specAt10 3 36
private theorem cFlags10_3_36 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_36 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_82 coordinateInput10_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_82 hCoordinate10_73]
  decide +kernel
private abbrev cSpec10_3_37 := specAt10 3 37
private theorem cFlags10_3_37 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_37 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_82 coordinateInput10_93 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_82 hCoordinate10_93]
  decide +kernel
private abbrev cSpec10_3_38 := specAt10 3 38
private theorem cFlags10_3_38 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_38 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_92 coordinateInput10_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_92 hCoordinate10_83]
  decide +kernel
private abbrev cSpec10_3_39 := specAt10 3 39
private theorem cFlags10_3_39 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_39 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_92 coordinateInput10_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_92 hCoordinate10_33]
  decide +kernel
private abbrev cSpec10_3_40 := specAt10 3 40
private theorem cFlags10_3_40 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_40 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_32 coordinateInput10_93 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_32 hCoordinate10_93]
  decide +kernel
private abbrev cSpec10_3_41 := specAt10 3 41
private theorem cFlags10_3_41 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_41 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_20

private abbrev cSpec10_3_42 := specAt10 3 42
private theorem cFlags10_3_42 : automaticFlags (trunkCatalog.states 10).context cSpec10_3_42 = [false, true, false, false] := by
  exact (automaticFlags_same _ _ cSpec10_1_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_21

private abbrev cSpec10_4_1 := specAt10 4 1
private theorem cFlags10_4_1 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_1 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_1

private abbrev cSpec10_4_2 := specAt10 4 2
private theorem cFlags10_4_2 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_2 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_2

private abbrev cSpec10_4_3 := specAt10 4 3
private theorem cFlags10_4_3 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_3 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_3

private abbrev cSpec10_4_4 := specAt10 4 4
private theorem cFlags10_4_4 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_4 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_4

private abbrev cSpec10_4_5 := specAt10 4 5
private theorem cFlags10_4_5 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_5 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_5

private abbrev cSpec10_4_6 := specAt10 4 6
private theorem cFlags10_4_6 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_6 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_6

private abbrev cSpec10_4_7 := specAt10 4 7
private theorem cFlags10_4_7 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_7 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_7

private abbrev cSpec10_4_8 := specAt10 4 8
private theorem cFlags10_4_8 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_8 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_8

private abbrev cSpec10_4_9 := specAt10 4 9
private theorem cFlags10_4_9 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_9 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_9

private abbrev cSpec10_4_10 := specAt10 4 10
private theorem cFlags10_4_10 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_10 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_10

private abbrev cSpec10_4_11 := specAt10 4 11
private theorem cFlags10_4_11 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_11 = (List.replicate 1 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_11

private abbrev cSpec10_4_12 := specAt10 4 12
private theorem cFlags10_4_12 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_12 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_12

private abbrev cSpec10_4_13 := specAt10 4 13
private theorem cFlags10_4_13 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_13 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_13

private abbrev cSpec10_4_14 := specAt10 4 14
private theorem cFlags10_4_14 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_14 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_14

private abbrev cSpec10_4_15 := specAt10 4 15
private theorem cFlags10_4_15 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_15 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_15

private abbrev cSpec10_4_16 := specAt10 4 16
private theorem cFlags10_4_16 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_16 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_16

private abbrev cSpec10_4_17 := specAt10 4 17
private theorem cFlags10_4_17 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_17

private abbrev cSpec10_4_18 := specAt10 4 18
private theorem cFlags10_4_18 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_18 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_18

private abbrev cSpec10_4_19 := specAt10 4 19
private theorem cFlags10_4_19 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_19 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_19

private abbrev cSpec10_4_20 := specAt10 4 20
private theorem cFlags10_4_20 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_20 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_20

private abbrev cSpec10_4_21 := specAt10 4 21
private theorem cFlags10_4_21 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_21 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_21

private abbrev cSpec10_4_22 := specAt10 4 22
private theorem cFlags10_4_22 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_22 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_22

private abbrev cSpec10_4_23 := specAt10 4 23
private theorem cFlags10_4_23 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_23 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_23

private abbrev cSpec10_4_24 := specAt10 4 24
private theorem cFlags10_4_24 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_24 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_24

private abbrev cSpec10_4_25 := specAt10 4 25
private theorem cFlags10_4_25 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_25 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_25

private abbrev cSpec10_4_26 := specAt10 4 26
private theorem cFlags10_4_26 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_11

private abbrev cSpec10_4_27 := specAt10 4 27
private theorem cFlags10_4_27 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec10_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_12

private abbrev cSpec10_4_28 := specAt10 4 28
private theorem cFlags10_4_28 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_13

private abbrev cSpec10_4_29 := specAt10 4 29
private theorem cFlags10_4_29 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_14

private abbrev cSpec10_4_30 := specAt10 4 30
private theorem cFlags10_4_30 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_15

private abbrev cSpec10_4_31 := specAt10 4 31
private theorem cFlags10_4_31 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_31 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_2_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_16

private abbrev cSpec10_4_32 := specAt10 4 32
private theorem cFlags10_4_32 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_32 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_2_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_17

private abbrev cSpec10_4_33 := specAt10 4 33
private theorem cFlags10_4_33 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_33 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_2_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_18

private abbrev cSpec10_4_34 := specAt10 4 34
private theorem cFlags10_4_34 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_34 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_2_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_19

private abbrev cSpec10_4_35 := specAt10 4 35
private theorem cFlags10_4_35 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_35 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_2_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_20

private abbrev cSpec10_4_36 := specAt10 4 36
private theorem cFlags10_4_36 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_36 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_2_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_21

private abbrev cSpec10_4_37 := specAt10 4 37
private theorem cFlags10_4_37 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_37 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_2_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_22

private abbrev cSpec10_4_38 := specAt10 4 38
private theorem cFlags10_4_38 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_38 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_2_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_23

private abbrev cSpec10_4_39 := specAt10 4 39
private theorem cFlags10_4_39 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_39 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_2_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_24

private abbrev cSpec10_4_40 := specAt10 4 40
private theorem cFlags10_4_40 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_40 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_2_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_25

private abbrev cSpec10_4_41 := specAt10 4 41
private theorem cFlags10_4_41 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_41 = (List.replicate 8 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_31

private abbrev cSpec10_4_42 := specAt10 4 42
private theorem cFlags10_4_42 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_42 = (List.replicate 5 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_32

private abbrev cSpec10_4_43 := specAt10 4 43
private theorem cFlags10_4_43 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_43 = (List.replicate 1 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_33 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_33

private abbrev cSpec10_4_44 := specAt10 4 44
private theorem cFlags10_4_44 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_44 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_34 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_34

private abbrev cSpec10_4_45 := specAt10 4 45
private theorem cFlags10_4_45 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_45 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_35 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_35

private abbrev cSpec10_4_46 := specAt10 4 46
private theorem cFlags10_4_46 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_46 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_36 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_36

private abbrev cSpec10_4_47 := specAt10 4 47
private theorem cFlags10_4_47 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_47 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_37 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_37

private abbrev cSpec10_4_48 := specAt10 4 48
private theorem cFlags10_4_48 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_48 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_38 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_38

private abbrev cSpec10_4_49 := specAt10 4 49
private theorem cFlags10_4_49 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_49 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_39 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_39

private abbrev cSpec10_4_50 := specAt10 4 50
private theorem cFlags10_4_50 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_50 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_40 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_40

private abbrev cSpec10_4_51 := specAt10 4 51
private theorem cFlags10_4_51 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_51 = [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false] := by
  exact (automaticFlags_same _ _ cSpec10_2_30 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_30

private abbrev cSpec10_4_52 := specAt10 4 52
private theorem cFlags10_4_52 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_52 = (List.replicate 1 false) := by
  exact (automaticFlags_same _ _ cSpec10_2_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_31

private abbrev cSpec10_4_53 := specAt10 4 53
private theorem cFlags10_4_53 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_53 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_20

private abbrev cSpec10_4_54 := specAt10 4 54
private theorem cFlags10_4_54 : automaticFlags (trunkCatalog.states 10).context cSpec10_4_54 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_2_33 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_33

private abbrev cSpec10_5_1 := specAt10 5 1
private theorem cFlags10_5_1 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_1 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_1

private abbrev cSpec10_5_2 := specAt10 5 2
private theorem cFlags10_5_2 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_2 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_2

private abbrev cSpec10_5_3 := specAt10 5 3
private theorem cFlags10_5_3 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_3 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_3

private abbrev cSpec10_5_4 := specAt10 5 4
private theorem cFlags10_5_4 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_4 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_4

private abbrev cSpec10_5_5 := specAt10 5 5
private theorem cFlags10_5_5 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_5 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_5

private abbrev cSpec10_5_6 := specAt10 5 6
private theorem cFlags10_5_6 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_6 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_6

private abbrev cSpec10_5_7 := specAt10 5 7
private theorem cFlags10_5_7 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_7 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_7

private abbrev cSpec10_5_8 := specAt10 5 8
private theorem cFlags10_5_8 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_8 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_8

private abbrev cSpec10_5_9 := specAt10 5 9
private theorem cFlags10_5_9 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_9 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_9

private abbrev cSpec10_5_10 := specAt10 5 10
private theorem cFlags10_5_10 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_10 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_10

private abbrev cSpec10_5_11 := specAt10 5 11
private theorem cFlags10_5_11 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_11 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_102 coordinateInput10_103 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_102 hCoordinate10_103]
  decide +kernel
private abbrev cSpec10_5_12 := specAt10 5 12
private theorem cFlags10_5_12 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_12 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_104 coordinateInput10_105 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_104 hCoordinate10_105]
  decide +kernel
private abbrev cSpec10_5_13 := specAt10 5 13
private theorem cFlags10_5_13 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_13 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_106 coordinateInput10_107 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_106 hCoordinate10_107]
  decide +kernel
private abbrev cSpec10_5_14 := specAt10 5 14
private theorem cFlags10_5_14 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_14 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_108 coordinateInput10_109 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_108 hCoordinate10_109]
  decide +kernel
private abbrev cSpec10_5_15 := specAt10 5 15
private theorem cFlags10_5_15 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_15 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_110 coordinateInput10_111 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_110 hCoordinate10_111]
  decide +kernel
private abbrev cSpec10_5_16 := specAt10 5 16
private theorem cFlags10_5_16 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_16 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_16

private abbrev cSpec10_5_17 := specAt10 5 17
private theorem cFlags10_5_17 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_17

private abbrev cSpec10_5_18 := specAt10 5 18
private theorem cFlags10_5_18 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_18 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_18

private abbrev cSpec10_5_19 := specAt10 5 19
private theorem cFlags10_5_19 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_19 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_19

private abbrev cSpec10_5_20 := specAt10 5 20
private theorem cFlags10_5_20 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_20 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_20

private abbrev cSpec10_5_21 := specAt10 5 21
private theorem cFlags10_5_21 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_21 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_21

private abbrev cSpec10_5_22 := specAt10 5 22
private theorem cFlags10_5_22 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_22 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_22

private abbrev cSpec10_5_23 := specAt10 5 23
private theorem cFlags10_5_23 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_23 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_23

private abbrev cSpec10_5_24 := specAt10 5 24
private theorem cFlags10_5_24 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_24 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_24

private abbrev cSpec10_5_25 := specAt10 5 25
private theorem cFlags10_5_25 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_25 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_25

private abbrev cSpec10_5_26 := specAt10 5 26
private theorem cFlags10_5_26 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_11

private abbrev cSpec10_5_27 := specAt10 5 27
private theorem cFlags10_5_27 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec10_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_12

private abbrev cSpec10_5_28 := specAt10 5 28
private theorem cFlags10_5_28 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_13

private abbrev cSpec10_5_29 := specAt10 5 29
private theorem cFlags10_5_29 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_14

private abbrev cSpec10_5_30 := specAt10 5 30
private theorem cFlags10_5_30 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_15

private abbrev cSpec10_5_31 := specAt10 5 31
private theorem cFlags10_5_31 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_31 = (List.replicate 8 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_31

private abbrev cSpec10_5_32 := specAt10 5 32
private theorem cFlags10_5_32 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_32 = (List.replicate 5 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_32

private abbrev cSpec10_5_33 := specAt10 5 33
private theorem cFlags10_5_33 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_33 = (List.replicate 2 true) := by
  rw [automaticFlags_cached _ _ coordinateInput10_62 coordinateInput10_103 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_62 hCoordinate10_103]
  decide +kernel
private abbrev cSpec10_5_34 := specAt10 5 34
private theorem cFlags10_5_34 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_34 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_102 coordinateInput10_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_102 hCoordinate10_63]
  decide +kernel
private abbrev cSpec10_5_35 := specAt10 5 35
private theorem cFlags10_5_35 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_35 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_102 coordinateInput10_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_102 hCoordinate10_83]
  decide +kernel
private abbrev cSpec10_5_36 := specAt10 5 36
private theorem cFlags10_5_36 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_36 = (List.replicate 8 false) := by
  rw [automaticFlags_cached _ _ coordinateInput10_82 coordinateInput10_103 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate10_82 hCoordinate10_103]
  decide +kernel
private abbrev cSpec10_5_37 := specAt10 5 37
private theorem cFlags10_5_37 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_37 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_37 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_37

private abbrev cSpec10_5_38 := specAt10 5 38
private theorem cFlags10_5_38 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_38 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_38 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_38

private abbrev cSpec10_5_39 := specAt10 5 39
private theorem cFlags10_5_39 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_39 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_39 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_39

private abbrev cSpec10_5_40 := specAt10 5 40
private theorem cFlags10_5_40 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_40 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_40 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_40

private abbrev cSpec10_5_41 := specAt10 5 41
private theorem cFlags10_5_41 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_41 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_20

private abbrev cSpec10_5_42 := specAt10 5 42
private theorem cFlags10_5_42 : automaticFlags (trunkCatalog.states 10).context cSpec10_5_42 = [false, true, false, false] := by
  exact (automaticFlags_same _ _ cSpec10_1_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_21

private abbrev cSpec10_6_1 := specAt10 6 1
private theorem cFlags10_6_1 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_1 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_1

private abbrev cSpec10_6_2 := specAt10 6 2
private theorem cFlags10_6_2 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_2 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_2

private abbrev cSpec10_6_3 := specAt10 6 3
private theorem cFlags10_6_3 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_3 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_3

private abbrev cSpec10_6_4 := specAt10 6 4
private theorem cFlags10_6_4 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_4 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_4

private abbrev cSpec10_6_5 := specAt10 6 5
private theorem cFlags10_6_5 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_5 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_5

private abbrev cSpec10_6_6 := specAt10 6 6
private theorem cFlags10_6_6 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_6 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_6

private abbrev cSpec10_6_7 := specAt10 6 7
private theorem cFlags10_6_7 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_7 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_7

private abbrev cSpec10_6_8 := specAt10 6 8
private theorem cFlags10_6_8 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_8 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_8

private abbrev cSpec10_6_9 := specAt10 6 9
private theorem cFlags10_6_9 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_9 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_9

private abbrev cSpec10_6_10 := specAt10 6 10
private theorem cFlags10_6_10 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_10 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_10

private abbrev cSpec10_6_11 := specAt10 6 11
private theorem cFlags10_6_11 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_11 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_5_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_5_11

private abbrev cSpec10_6_12 := specAt10 6 12
private theorem cFlags10_6_12 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_12 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec10_5_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_5_12

private abbrev cSpec10_6_13 := specAt10 6 13
private theorem cFlags10_6_13 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_13 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_5_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_5_13

private abbrev cSpec10_6_14 := specAt10 6 14
private theorem cFlags10_6_14 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_14 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_5_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_5_14

private abbrev cSpec10_6_15 := specAt10 6 15
private theorem cFlags10_6_15 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_15 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_5_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_5_15

private abbrev cSpec10_6_16 := specAt10 6 16
private theorem cFlags10_6_16 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_16 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_16

private abbrev cSpec10_6_17 := specAt10 6 17
private theorem cFlags10_6_17 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_17

private abbrev cSpec10_6_18 := specAt10 6 18
private theorem cFlags10_6_18 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_18 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_18

private abbrev cSpec10_6_19 := specAt10 6 19
private theorem cFlags10_6_19 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_19 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_19

private abbrev cSpec10_6_20 := specAt10 6 20
private theorem cFlags10_6_20 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_20 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_20

private abbrev cSpec10_6_21 := specAt10 6 21
private theorem cFlags10_6_21 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_21 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_21

private abbrev cSpec10_6_22 := specAt10 6 22
private theorem cFlags10_6_22 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_22 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_22

private abbrev cSpec10_6_23 := specAt10 6 23
private theorem cFlags10_6_23 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_23 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_23

private abbrev cSpec10_6_24 := specAt10 6 24
private theorem cFlags10_6_24 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_24 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_24

private abbrev cSpec10_6_25 := specAt10 6 25
private theorem cFlags10_6_25 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_25 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_25

private abbrev cSpec10_6_26 := specAt10 6 26
private theorem cFlags10_6_26 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_11

private abbrev cSpec10_6_27 := specAt10 6 27
private theorem cFlags10_6_27 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec10_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_12

private abbrev cSpec10_6_28 := specAt10 6 28
private theorem cFlags10_6_28 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_13

private abbrev cSpec10_6_29 := specAt10 6 29
private theorem cFlags10_6_29 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_14

private abbrev cSpec10_6_30 := specAt10 6 30
private theorem cFlags10_6_30 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_1_15

private abbrev cSpec10_6_31 := specAt10 6 31
private theorem cFlags10_6_31 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_31 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_2_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_16

private abbrev cSpec10_6_32 := specAt10 6 32
private theorem cFlags10_6_32 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_32 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_2_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_17

private abbrev cSpec10_6_33 := specAt10 6 33
private theorem cFlags10_6_33 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_33 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_2_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_18

private abbrev cSpec10_6_34 := specAt10 6 34
private theorem cFlags10_6_34 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_34 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_2_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_19

private abbrev cSpec10_6_35 := specAt10 6 35
private theorem cFlags10_6_35 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_35 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_2_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_20

private abbrev cSpec10_6_36 := specAt10 6 36
private theorem cFlags10_6_36 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_36 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_2_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_21

private abbrev cSpec10_6_37 := specAt10 6 37
private theorem cFlags10_6_37 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_37 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_2_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_22

private abbrev cSpec10_6_38 := specAt10 6 38
private theorem cFlags10_6_38 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_38 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_2_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_23

private abbrev cSpec10_6_39 := specAt10 6 39
private theorem cFlags10_6_39 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_39 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec10_2_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_24

private abbrev cSpec10_6_40 := specAt10 6 40
private theorem cFlags10_6_40 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_40 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec10_2_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_25

private abbrev cSpec10_6_41 := specAt10 6 41
private theorem cFlags10_6_41 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_41 = (List.replicate 8 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_31

private abbrev cSpec10_6_42 := specAt10 6 42
private theorem cFlags10_6_42 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_42 = (List.replicate 5 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_32

private abbrev cSpec10_6_43 := specAt10 6 43
private theorem cFlags10_6_43 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_43 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec10_5_33 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_5_33

private abbrev cSpec10_6_44 := specAt10 6 44
private theorem cFlags10_6_44 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_44 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec10_5_34 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_5_34

private abbrev cSpec10_6_45 := specAt10 6 45
private theorem cFlags10_6_45 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_45 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec10_5_35 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_5_35

private abbrev cSpec10_6_46 := specAt10 6 46
private theorem cFlags10_6_46 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_46 = (List.replicate 8 false) := by
  exact (automaticFlags_same _ _ cSpec10_5_36 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_5_36

private abbrev cSpec10_6_47 := specAt10 6 47
private theorem cFlags10_6_47 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_47 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_3_37 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_37

private abbrev cSpec10_6_48 := specAt10 6 48
private theorem cFlags10_6_48 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_48 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_38 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_38

private abbrev cSpec10_6_49 := specAt10 6 49
private theorem cFlags10_6_49 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_49 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_39 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_39

private abbrev cSpec10_6_50 := specAt10 6 50
private theorem cFlags10_6_50 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_50 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec10_3_40 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_3_40

private abbrev cSpec10_6_51 := specAt10 6 51
private theorem cFlags10_6_51 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_51 = [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false] := by
  exact (automaticFlags_same _ _ cSpec10_2_30 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_30

private abbrev cSpec10_6_52 := specAt10 6 52
private theorem cFlags10_6_52 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_52 = (List.replicate 1 false) := by
  exact (automaticFlags_same _ _ cSpec10_2_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_31

private abbrev cSpec10_6_53 := specAt10 6 53
private theorem cFlags10_6_53 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_53 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec10_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_0_20

private abbrev cSpec10_6_54 := specAt10 6 54
private theorem cFlags10_6_54 : automaticFlags (trunkCatalog.states 10).context cSpec10_6_54 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec10_2_33 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags10_2_33

private theorem keys_eq : coverageKeys (trunkCatalog.states 10) = checkedKeys := by
  rfl
private theorem tasks_eq : coverageTasks (trunkCatalog.states 10) = checkedTasks := by
  rw [← coverageTasksProjection_eq]
  change [(0,[(1, (automaticFlags (trunkCatalog.states 10).context cSpec10_0_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 10).context cSpec10_0_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 10).context cSpec10_0_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 10).context cSpec10_0_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 10).context cSpec10_0_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 10).context cSpec10_0_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 10).context cSpec10_0_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 10).context cSpec10_0_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 10).context cSpec10_0_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 10).context cSpec10_0_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 10).context cSpec10_0_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 10).context cSpec10_0_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 10).context cSpec10_0_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 10).context cSpec10_0_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 10).context cSpec10_0_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 10).context cSpec10_0_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 10).context cSpec10_0_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 10).context cSpec10_0_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 10).context cSpec10_0_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 10).context cSpec10_0_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 10).context cSpec10_0_21).zipIdx.map Prod.swap)]),(1,[(1, (automaticFlags (trunkCatalog.states 10).context cSpec10_1_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 10).context cSpec10_1_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 10).context cSpec10_1_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 10).context cSpec10_1_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 10).context cSpec10_1_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 10).context cSpec10_1_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 10).context cSpec10_1_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 10).context cSpec10_1_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 10).context cSpec10_1_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 10).context cSpec10_1_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 10).context cSpec10_1_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 10).context cSpec10_1_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 10).context cSpec10_1_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 10).context cSpec10_1_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 10).context cSpec10_1_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 10).context cSpec10_1_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 10).context cSpec10_1_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 10).context cSpec10_1_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 10).context cSpec10_1_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 10).context cSpec10_1_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 10).context cSpec10_1_21).zipIdx.map Prod.swap)]),(2,[(1, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 10).context cSpec10_2_33).zipIdx.map Prod.swap)]),(3,[(1, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 10).context cSpec10_3_42).zipIdx.map Prod.swap)]),(4,[(1, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_42).zipIdx.map Prod.swap),(43, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_43).zipIdx.map Prod.swap),(44, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_44).zipIdx.map Prod.swap),(45, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_45).zipIdx.map Prod.swap),(46, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_46).zipIdx.map Prod.swap),(47, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_47).zipIdx.map Prod.swap),(48, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_48).zipIdx.map Prod.swap),(49, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_49).zipIdx.map Prod.swap),(50, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_50).zipIdx.map Prod.swap),(51, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_51).zipIdx.map Prod.swap),(52, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_52).zipIdx.map Prod.swap),(53, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_53).zipIdx.map Prod.swap),(54, (automaticFlags (trunkCatalog.states 10).context cSpec10_4_54).zipIdx.map Prod.swap)]),(5,[(1, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 10).context cSpec10_5_42).zipIdx.map Prod.swap)]),(6,[(1, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_42).zipIdx.map Prod.swap),(43, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_43).zipIdx.map Prod.swap),(44, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_44).zipIdx.map Prod.swap),(45, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_45).zipIdx.map Prod.swap),(46, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_46).zipIdx.map Prod.swap),(47, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_47).zipIdx.map Prod.swap),(48, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_48).zipIdx.map Prod.swap),(49, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_49).zipIdx.map Prod.swap),(50, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_50).zipIdx.map Prod.swap),(51, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_51).zipIdx.map Prod.swap),(52, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_52).zipIdx.map Prod.swap),(53, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_53).zipIdx.map Prod.swap),(54, (automaticFlags (trunkCatalog.states 10).context cSpec10_6_54).zipIdx.map Prod.swap)])] = checkedTasks
  rw [cFlags10_0_1, cFlags10_0_2, cFlags10_0_3, cFlags10_0_4, cFlags10_0_5, cFlags10_0_6, cFlags10_0_7, cFlags10_0_8, cFlags10_0_9, cFlags10_0_10, cFlags10_0_11, cFlags10_0_12, cFlags10_0_13, cFlags10_0_14, cFlags10_0_15, cFlags10_0_16, cFlags10_0_17, cFlags10_0_18, cFlags10_0_19, cFlags10_0_20, cFlags10_0_21, cFlags10_1_1, cFlags10_1_2, cFlags10_1_3, cFlags10_1_4, cFlags10_1_5, cFlags10_1_6, cFlags10_1_7, cFlags10_1_8, cFlags10_1_9, cFlags10_1_10, cFlags10_1_11, cFlags10_1_12, cFlags10_1_13, cFlags10_1_14, cFlags10_1_15, cFlags10_1_16, cFlags10_1_17, cFlags10_1_18, cFlags10_1_19, cFlags10_1_20, cFlags10_1_21, cFlags10_2_1, cFlags10_2_2, cFlags10_2_3, cFlags10_2_4, cFlags10_2_5, cFlags10_2_6, cFlags10_2_7, cFlags10_2_8, cFlags10_2_9, cFlags10_2_10, cFlags10_2_11, cFlags10_2_12, cFlags10_2_13, cFlags10_2_14, cFlags10_2_15, cFlags10_2_16, cFlags10_2_17, cFlags10_2_18, cFlags10_2_19, cFlags10_2_20, cFlags10_2_21, cFlags10_2_22, cFlags10_2_23, cFlags10_2_24, cFlags10_2_25, cFlags10_2_26, cFlags10_2_27, cFlags10_2_28, cFlags10_2_29, cFlags10_2_30, cFlags10_2_31, cFlags10_2_32, cFlags10_2_33, cFlags10_3_1, cFlags10_3_2, cFlags10_3_3, cFlags10_3_4, cFlags10_3_5, cFlags10_3_6, cFlags10_3_7, cFlags10_3_8, cFlags10_3_9, cFlags10_3_10, cFlags10_3_11, cFlags10_3_12, cFlags10_3_13, cFlags10_3_14, cFlags10_3_15, cFlags10_3_16, cFlags10_3_17, cFlags10_3_18, cFlags10_3_19, cFlags10_3_20, cFlags10_3_21, cFlags10_3_22, cFlags10_3_23, cFlags10_3_24, cFlags10_3_25, cFlags10_3_26, cFlags10_3_27, cFlags10_3_28, cFlags10_3_29, cFlags10_3_30, cFlags10_3_31, cFlags10_3_32, cFlags10_3_33, cFlags10_3_34, cFlags10_3_35, cFlags10_3_36, cFlags10_3_37, cFlags10_3_38, cFlags10_3_39, cFlags10_3_40, cFlags10_3_41, cFlags10_3_42, cFlags10_4_1, cFlags10_4_2, cFlags10_4_3, cFlags10_4_4, cFlags10_4_5, cFlags10_4_6, cFlags10_4_7, cFlags10_4_8, cFlags10_4_9, cFlags10_4_10, cFlags10_4_11, cFlags10_4_12, cFlags10_4_13, cFlags10_4_14, cFlags10_4_15, cFlags10_4_16, cFlags10_4_17, cFlags10_4_18, cFlags10_4_19, cFlags10_4_20, cFlags10_4_21, cFlags10_4_22, cFlags10_4_23, cFlags10_4_24, cFlags10_4_25, cFlags10_4_26, cFlags10_4_27, cFlags10_4_28, cFlags10_4_29, cFlags10_4_30, cFlags10_4_31, cFlags10_4_32, cFlags10_4_33, cFlags10_4_34, cFlags10_4_35, cFlags10_4_36, cFlags10_4_37, cFlags10_4_38, cFlags10_4_39, cFlags10_4_40, cFlags10_4_41, cFlags10_4_42, cFlags10_4_43, cFlags10_4_44, cFlags10_4_45, cFlags10_4_46, cFlags10_4_47, cFlags10_4_48, cFlags10_4_49, cFlags10_4_50, cFlags10_4_51, cFlags10_4_52, cFlags10_4_53, cFlags10_4_54, cFlags10_5_1, cFlags10_5_2, cFlags10_5_3, cFlags10_5_4, cFlags10_5_5, cFlags10_5_6, cFlags10_5_7, cFlags10_5_8, cFlags10_5_9, cFlags10_5_10, cFlags10_5_11, cFlags10_5_12, cFlags10_5_13, cFlags10_5_14, cFlags10_5_15, cFlags10_5_16, cFlags10_5_17, cFlags10_5_18, cFlags10_5_19, cFlags10_5_20, cFlags10_5_21, cFlags10_5_22, cFlags10_5_23, cFlags10_5_24, cFlags10_5_25, cFlags10_5_26, cFlags10_5_27, cFlags10_5_28, cFlags10_5_29, cFlags10_5_30, cFlags10_5_31, cFlags10_5_32, cFlags10_5_33, cFlags10_5_34, cFlags10_5_35, cFlags10_5_36, cFlags10_5_37, cFlags10_5_38, cFlags10_5_39, cFlags10_5_40, cFlags10_5_41, cFlags10_5_42, cFlags10_6_1, cFlags10_6_2, cFlags10_6_3, cFlags10_6_4, cFlags10_6_5, cFlags10_6_6, cFlags10_6_7, cFlags10_6_8, cFlags10_6_9, cFlags10_6_10, cFlags10_6_11, cFlags10_6_12, cFlags10_6_13, cFlags10_6_14, cFlags10_6_15, cFlags10_6_16, cFlags10_6_17, cFlags10_6_18, cFlags10_6_19, cFlags10_6_20, cFlags10_6_21, cFlags10_6_22, cFlags10_6_23, cFlags10_6_24, cFlags10_6_25, cFlags10_6_26, cFlags10_6_27, cFlags10_6_28, cFlags10_6_29, cFlags10_6_30, cFlags10_6_31, cFlags10_6_32, cFlags10_6_33, cFlags10_6_34, cFlags10_6_35, cFlags10_6_36, cFlags10_6_37, cFlags10_6_38, cFlags10_6_39, cFlags10_6_40, cFlags10_6_41, cFlags10_6_42, cFlags10_6_43, cFlags10_6_44, cFlags10_6_45, cFlags10_6_46, cFlags10_6_47, cFlags10_6_48, cFlags10_6_49, cFlags10_6_50, cFlags10_6_51, cFlags10_6_52, cFlags10_6_53, cFlags10_6_54]
  rfl
private theorem parents_length : (trunkRawParents (trunkCatalog.states 10).context).length = 100 := by
  decide +kernel
private theorem table_checked : coverageTable checkedKeys checkedTasks 100 := by
  apply coverageRemainder_sound _ _ _ [[74], [], [74, 99], [99], [99], [99], []]
  unfold coverageRemainder parentsFor
  decide +kernel

theorem solution : trunkCoverage trunkCatalog 10 := by
  apply coverageTable_sound 10
  · unfold certRectangleValid; decide +kernel
  · decide +kernel
  · rw [keys_eq, tasks_eq, parents_length]
    exact table_checked
#print axioms solution
