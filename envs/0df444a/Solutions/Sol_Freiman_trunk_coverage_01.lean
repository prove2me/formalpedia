-- Prove2me | solution 1 for Freiman.trunk_coverage_01
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:10:36.740511+00:00
-- url     : https://prove2.me/submissions/596e034f-0d2a-4f37-8d17-125d97c0c740

import Definitions.Def_Freiman_trunkGeometry
import Definitions.Def_Freiman_trunkFast
import Mathlib.Tactic
open Freiman
set_option Elab.async false
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

private def coordinateFields1 : Array CertField := #[⟨(4/13),(1/13),(0/1),(0/1)⟩,⟨(1/2),(1/6),(0/1),(0/1)⟩,⟨(52/73),(1/73),(0/1),(0/1)⟩,⟨(89/214),(1/214),(0/1),(0/1)⟩,⟨(9/13),(-1/13),(0/1),(0/1)⟩,⟨(2/1),(-1/1),(0/1),(0/1)⟩,⟨(15/37),(-1/37),(0/1),(0/1)⟩,⟨(125/214),(-1/214),(0/1),(0/1)⟩,⟨(66/179),(-1/537),(0/1),(0/1)⟩,⟨(22/37),(1/37),(0/1),(0/1)⟩,⟨(113/179),(1/537),(0/1),(0/1)⟩,⟨(17/22),(-1/22),(0/1),(0/1)⟩,⟨(101/143),(-1/429),(0/1),(0/1)⟩,⟨(735/1006),(1/1006),(0/1),(0/1)⟩,⟨(35/94),(1/94),(0/1),(0/1)⟩,⟨(553/1429),(1/1429),(0/1),(0/1)⟩,⟨(10/23),(-1/69),(0/1),(0/1)⟩,⟨(517/1249),(-1/1249),(0/1),(0/1)⟩,⟨(1272/3013),(1/3013),(0/1),(0/1)⟩,⟨(5/22),(1/22),(0/1),(0/1)⟩,⟨(42/143),(1/429),(0/1),(0/1)⟩,⟨(271/1006),(-1/1006),(0/1),(0/1)⟩,⟨(16/59),(1/177),(0/1),(0/1)⟩,⟨(767/2749),(1/2749),(0/1),(0/1)⟩,⟨(43/142),(-1/142),(0/1),(0/1)⟩,⟨(731/2497),(-1/2497),(0/1),(0/1)⟩,⟨(1809/6094),(1/6094),(0/1),(0/1)⟩,⟨(3289/10753),(1/10753),(0/1),(0/1)⟩,⟨(71/229),(-1/229),(0/1),(0/1)⟩,⟨(1413/4654),(-1/4654),(0/1),(0/1)⟩,⟨(6697/22079),(-1/66237),(0/1),(0/1)⟩,⟨(469/1549),(1/1549),(0/1),(0/1)⟩,⟨(579/1894),(-1/1894),(0/1),(0/1)⟩,⟨(9014/29557),(-1/29557),(0/1),(0/1)⟩,⟨(13/23),(1/69),(0/1),(0/1)⟩,⟨(732/1249),(1/1249),(0/1),(0/1)⟩,⟨(59/94),(-1/94),(0/1),(0/1)⟩]
private abbrev coordinateInput1_0 : LowerPair × Bool × Bool := (([2], []), true, false)
private def coordinateCodes1_0 : List (ℕ × ℕ) := [(0, 1), (0, 1), (0, 2), (0, 1), (3, 1)]
private abbrev coordinateInput1_1 : LowerPair × Bool × Bool := (([1], []), false, false)
private def coordinateCodes1_1 : List (ℕ × ℕ) := [(4, 5), (4, 6), (4, 5), (7, 5), (4, 5)]
private abbrev coordinateInput1_2 : LowerPair × Bool × Bool := (([1], []), true, false)
private def coordinateCodes1_2 : List (ℕ × ℕ) := [(1, 1), (1, 1), (1, 2), (1, 1), (2, 1)]
private abbrev coordinateInput1_3 : LowerPair × Bool × Bool := (([2], []), false, false)
private def coordinateCodes1_3 : List (ℕ × ℕ) := [(6, 5), (6, 6), (6, 5), (8, 5), (6, 5)]
private abbrev coordinateInput1_4 : LowerPair × Bool × Bool := (([1, 1], []), true, false)
private def coordinateCodes1_4 : List (ℕ × ℕ) := [(9, 1), (9, 2), (9, 1), (10, 1)]
private abbrev coordinateInput1_5 : LowerPair × Bool × Bool := (([1, 2], []), false, false)
private def coordinateCodes1_5 : List (ℕ × ℕ) := [(11, 5), (11, 6), (11, 5), (12, 5)]
private abbrev coordinateInput1_6 : LowerPair × Bool × Bool := (([1, 2], []), true, false)
private def coordinateCodes1_6 : List (ℕ × ℕ) := [(2, 1), (2, 2), (2, 1), (13, 1)]
private abbrev coordinateInput1_7 : LowerPair × Bool × Bool := (([1, 1], []), false, false)
private def coordinateCodes1_7 : List (ℕ × ℕ) := [(4, 5), (4, 6), (4, 5), (7, 5)]
private abbrev coordinateInput1_8 : LowerPair × Bool × Bool := (([1], [1]), true, true)
private def coordinateCodes1_8 : List (ℕ × ℕ) := [(1, 1), (1, 2), (1, 1), (2, 1)]
private abbrev coordinateInput1_9 : LowerPair × Bool × Bool := (([1], [2]), false, true)
private def coordinateCodes1_9 : List (ℕ × ℕ) := [(4, 6), (4, 8), (4, 6), (7, 6)]
private abbrev coordinateInput1_10 : LowerPair × Bool × Bool := (([1], [2]), true, true)
private def coordinateCodes1_10 : List (ℕ × ℕ) := [(1, 0), (1, 3), (1, 0), (2, 0)]
private abbrev coordinateInput1_11 : LowerPair × Bool × Bool := (([1], [1]), false, true)
private def coordinateCodes1_11 : List (ℕ × ℕ) := [(4, 4), (4, 7), (4, 4), (7, 4)]
private abbrev coordinateInput1_12 : LowerPair × Bool × Bool := (([2, 1], []), true, false)
private def coordinateCodes1_12 : List (ℕ × ℕ) := [(14, 1), (14, 2), (14, 1), (15, 1)]
private abbrev coordinateInput1_13 : LowerPair × Bool × Bool := (([2, 2], []), false, false)
private def coordinateCodes1_13 : List (ℕ × ℕ) := [(16, 5), (16, 6), (16, 5), (17, 5)]
private abbrev coordinateInput1_14 : LowerPair × Bool × Bool := (([2, 2], []), true, false)
private def coordinateCodes1_14 : List (ℕ × ℕ) := [(3, 1), (3, 2), (3, 1), (18, 1)]
private abbrev coordinateInput1_15 : LowerPair × Bool × Bool := (([2, 1], []), false, false)
private def coordinateCodes1_15 : List (ℕ × ℕ) := [(6, 5), (6, 6), (6, 5), (8, 5)]
private abbrev coordinateInput1_16 : LowerPair × Bool × Bool := (([2], [1]), true, true)
private def coordinateCodes1_16 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 1), (3, 1)]
private abbrev coordinateInput1_17 : LowerPair × Bool × Bool := (([2], [2]), false, true)
private def coordinateCodes1_17 : List (ℕ × ℕ) := [(6, 6), (6, 8), (6, 6), (8, 6)]
private abbrev coordinateInput1_18 : LowerPair × Bool × Bool := (([2], [2]), true, true)
private def coordinateCodes1_18 : List (ℕ × ℕ) := [(0, 0), (0, 3), (0, 0), (3, 0)]
private abbrev coordinateInput1_19 : LowerPair × Bool × Bool := (([2], [1]), false, true)
private def coordinateCodes1_19 : List (ℕ × ℕ) := [(6, 4), (6, 7), (6, 4), (8, 4)]
private abbrev coordinateInput1_20 : LowerPair × Bool × Bool := (([3], []), true, false)
private def coordinateCodes1_20 : List (ℕ × ℕ) := [(19, 1), (19, 1), (19, 2), (19, 1), (20, 1)]
private abbrev coordinateInput1_21 : LowerPair × Bool × Bool := (([3], []), false, false)
private def coordinateCodes1_21 : List (ℕ × ℕ) := [(21, 5), (21, 5)]
private abbrev coordinateInput1_22 : LowerPair × Bool × Bool := (([3, 1], []), true, false)
private def coordinateCodes1_22 : List (ℕ × ℕ) := [(22, 1), (22, 2), (22, 1), (23, 1)]
private abbrev coordinateInput1_23 : LowerPair × Bool × Bool := (([3, 2], []), false, false)
private def coordinateCodes1_23 : List (ℕ × ℕ) := [(24, 5), (24, 6), (24, 5), (25, 5)]
private abbrev coordinateInput1_24 : LowerPair × Bool × Bool := (([3, 2], []), true, false)
private def coordinateCodes1_24 : List (ℕ × ℕ) := [(20, 1), (20, 2), (20, 1), (26, 1)]
private abbrev coordinateInput1_25 : LowerPair × Bool × Bool := (([3, 1], []), false, false)
private def coordinateCodes1_25 : List (ℕ × ℕ) := [(21, 5)]
private abbrev coordinateInput1_26 : LowerPair × Bool × Bool := (([3], [1]), true, true)
private def coordinateCodes1_26 : List (ℕ × ℕ) := [(19, 1), (19, 2), (19, 1), (20, 1)]
private abbrev coordinateInput1_27 : LowerPair × Bool × Bool := (([3], [2]), false, true)
private def coordinateCodes1_27 : List (ℕ × ℕ) := [(21, 6)]
private abbrev coordinateInput1_28 : LowerPair × Bool × Bool := (([3], [2]), true, true)
private def coordinateCodes1_28 : List (ℕ × ℕ) := [(19, 0), (19, 3), (19, 0), (20, 0)]
private abbrev coordinateInput1_29 : LowerPair × Bool × Bool := (([3], [1]), false, true)
private def coordinateCodes1_29 : List (ℕ × ℕ) := [(21, 4)]
private abbrev coordinateInput1_30 : LowerPair × Bool × Bool := (([], []), true, false)
private def coordinateCodes1_30 : List (ℕ × ℕ) := [(1, 1), (1, 2), (1, 1), (2, 1)]
private abbrev coordinateInput1_31 : LowerPair × Bool × Bool := (([], []), false, false)
private def coordinateCodes1_31 : List (ℕ × ℕ) := [(5, 5), (5, 6), (5, 5), (6, 5)]
private abbrev coordinateInput1_32 : LowerPair × Bool × Bool := (([3], [2]), true, false)
private def coordinateCodes1_32 : List (ℕ × ℕ) := [(19, 0), (19, 3), (19, 0), (20, 0)]
private abbrev coordinateInput1_33 : LowerPair × Bool × Bool := (([3], [2]), false, false)
private def coordinateCodes1_33 : List (ℕ × ℕ) := [(21, 6)]
private abbrev coordinateInput1_34 : LowerPair × Bool × Bool := (([3, 1], [2]), true, false)
private def coordinateCodes1_34 : List (ℕ × ℕ) := [(22, 0), (22, 3), (22, 0), (23, 0), (22, 0)]
private abbrev coordinateInput1_35 : LowerPair × Bool × Bool := (([3, 2], [2]), false, false)
private def coordinateCodes1_35 : List (ℕ × ℕ) := [(24, 6), (24, 6), (24, 8), (24, 6), (25, 6)]
private abbrev coordinateInput1_36 : LowerPair × Bool × Bool := (([3, 2], [2]), true, false)
private def coordinateCodes1_36 : List (ℕ × ℕ) := [(20, 0), (20, 3), (20, 0), (26, 0), (20, 0)]
private abbrev coordinateInput1_37 : LowerPair × Bool × Bool := (([3, 1], [2]), false, false)
private def coordinateCodes1_37 : List (ℕ × ℕ) := [(21, 6), (21, 6)]
private abbrev coordinateInput1_38 : LowerPair × Bool × Bool := (([3], [2, 1]), true, true)
private def coordinateCodes1_38 : List (ℕ × ℕ) := [(19, 14), (19, 14), (19, 15), (19, 14), (20, 14)]
private abbrev coordinateInput1_39 : LowerPair × Bool × Bool := (([3], [2, 2]), false, true)
private def coordinateCodes1_39 : List (ℕ × ℕ) := [(21, 16), (21, 16)]
private abbrev coordinateInput1_40 : LowerPair × Bool × Bool := (([3], [2, 2]), true, true)
private def coordinateCodes1_40 : List (ℕ × ℕ) := [(19, 3), (19, 3), (19, 18), (19, 3), (20, 3)]
private abbrev coordinateInput1_41 : LowerPair × Bool × Bool := (([3], [2, 1]), false, true)
private def coordinateCodes1_41 : List (ℕ × ℕ) := [(21, 6), (21, 6)]
private abbrev coordinateInput1_42 : LowerPair × Bool × Bool := (([3, 3], [3, 3]), true, false)
private def coordinateCodes1_42 : List (ℕ × ℕ) := [(27, 27)]
private abbrev coordinateInput1_43 : LowerPair × Bool × Bool := (([3, 3], [3, 3]), false, false)
private def coordinateCodes1_43 : List (ℕ × ℕ) := [(28, 28), (28, 29), (28, 28), (29, 28)]
private abbrev coordinateInput1_44 : LowerPair × Bool × Bool := (([3, 3, 1], [3, 3]), true, false)
private def coordinateCodes1_44 : List (ℕ × ℕ) := [(27, 27), (27, 27)]
private abbrev coordinateInput1_45 : LowerPair × Bool × Bool := (([3, 3, 2], [3, 3]), false, false)
private def coordinateCodes1_45 : List (ℕ × ℕ) := [(29, 28), (29, 29), (29, 28), (30, 28), (29, 28)]
private abbrev coordinateInput1_46 : LowerPair × Bool × Bool := (([3, 3, 2], [3, 3]), true, false)
private def coordinateCodes1_46 : List (ℕ × ℕ) := [(31, 27), (31, 27)]
private abbrev coordinateInput1_47 : LowerPair × Bool × Bool := (([3, 3, 1], [3, 3]), false, false)
private def coordinateCodes1_47 : List (ℕ × ℕ) := [(32, 28), (32, 29), (32, 28), (33, 28), (32, 28)]
private abbrev coordinateInput1_48 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 1]), true, true)
private def coordinateCodes1_48 : List (ℕ × ℕ) := [(27, 27), (27, 27)]
private abbrev coordinateInput1_49 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 2]), false, true)
private def coordinateCodes1_49 : List (ℕ × ℕ) := [(28, 29), (28, 29), (28, 30), (28, 29), (29, 29)]
private abbrev coordinateInput1_50 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 2]), true, true)
private def coordinateCodes1_50 : List (ℕ × ℕ) := [(27, 31), (27, 31)]
private abbrev coordinateInput1_51 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 1]), false, true)
private def coordinateCodes1_51 : List (ℕ × ℕ) := [(28, 32), (28, 32), (28, 33), (28, 32), (29, 32)]
private abbrev coordinateInput1_52 : LowerPair × Bool × Bool := (([3], [3]), true, false)
private def coordinateCodes1_52 : List (ℕ × ℕ) := [(19, 19), (19, 20), (19, 19), (20, 19)]
private abbrev coordinateInput1_53 : LowerPair × Bool × Bool := (([3], [3]), false, false)
private def coordinateCodes1_53 : List (ℕ × ℕ) := [(21, 21)]
private abbrev coordinateInput1_54 : LowerPair × Bool × Bool := (([3, 1], [3]), true, false)
private def coordinateCodes1_54 : List (ℕ × ℕ) := [(22, 19), (22, 20), (22, 19), (23, 19), (22, 19)]
private abbrev coordinateInput1_55 : LowerPair × Bool × Bool := (([3, 2], [3]), false, false)
private def coordinateCodes1_55 : List (ℕ × ℕ) := [(24, 21), (24, 21)]
private abbrev coordinateInput1_56 : LowerPair × Bool × Bool := (([3, 2], [3]), true, false)
private def coordinateCodes1_56 : List (ℕ × ℕ) := [(20, 19), (20, 20), (20, 19), (26, 19), (20, 19)]
private abbrev coordinateInput1_57 : LowerPair × Bool × Bool := (([3, 1], [3]), false, false)
private def coordinateCodes1_57 : List (ℕ × ℕ) := [(21, 21), (21, 21)]
private abbrev coordinateInput1_58 : LowerPair × Bool × Bool := (([3], [3, 1]), true, true)
private def coordinateCodes1_58 : List (ℕ × ℕ) := [(19, 22), (19, 22), (19, 23), (19, 22), (20, 22)]
private abbrev coordinateInput1_59 : LowerPair × Bool × Bool := (([3], [3, 2]), false, true)
private def coordinateCodes1_59 : List (ℕ × ℕ) := [(21, 24), (21, 24)]
private abbrev coordinateInput1_60 : LowerPair × Bool × Bool := (([3], [3, 2]), true, true)
private def coordinateCodes1_60 : List (ℕ × ℕ) := [(19, 20), (19, 20), (19, 26), (19, 20), (20, 20)]
private abbrev coordinateInput1_61 : LowerPair × Bool × Bool := (([3], [3, 1]), false, true)
private def coordinateCodes1_61 : List (ℕ × ℕ) := [(21, 21), (21, 21)]
private abbrev coordinateInput1_62 : LowerPair × Bool × Bool := (([2], [1]), true, false)
private def coordinateCodes1_62 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 1), (3, 1)]
private abbrev coordinateInput1_63 : LowerPair × Bool × Bool := (([2], [1]), false, false)
private def coordinateCodes1_63 : List (ℕ × ℕ) := [(6, 4), (6, 7), (6, 4), (8, 4)]
private abbrev coordinateInput1_64 : LowerPair × Bool × Bool := (([2, 1], [1]), true, false)
private def coordinateCodes1_64 : List (ℕ × ℕ) := [(14, 1), (14, 2), (14, 1), (15, 1), (14, 1)]
private abbrev coordinateInput1_65 : LowerPair × Bool × Bool := (([2, 2], [1]), false, false)
private def coordinateCodes1_65 : List (ℕ × ℕ) := [(16, 4), (16, 4), (16, 7), (16, 4), (17, 4)]
private abbrev coordinateInput1_66 : LowerPair × Bool × Bool := (([2, 2], [1]), true, false)
private def coordinateCodes1_66 : List (ℕ × ℕ) := [(3, 1), (3, 2), (3, 1), (18, 1), (3, 1)]
private abbrev coordinateInput1_67 : LowerPair × Bool × Bool := (([2, 1], [1]), false, false)
private def coordinateCodes1_67 : List (ℕ × ℕ) := [(6, 4), (6, 4), (6, 7), (6, 4), (8, 4)]
private abbrev coordinateInput1_68 : LowerPair × Bool × Bool := (([2], [1, 1]), true, true)
private def coordinateCodes1_68 : List (ℕ × ℕ) := [(0, 9), (0, 9), (0, 10), (0, 9), (3, 9)]
private abbrev coordinateInput1_69 : LowerPair × Bool × Bool := (([2], [1, 2]), false, true)
private def coordinateCodes1_69 : List (ℕ × ℕ) := [(6, 11), (6, 12), (6, 11), (8, 11), (6, 11)]
private abbrev coordinateInput1_70 : LowerPair × Bool × Bool := (([2], [1, 2]), true, true)
private def coordinateCodes1_70 : List (ℕ × ℕ) := [(0, 2), (0, 2), (0, 13), (0, 2), (3, 2)]
private abbrev coordinateInput1_71 : LowerPair × Bool × Bool := (([2], [1, 1]), false, true)
private def coordinateCodes1_71 : List (ℕ × ℕ) := [(6, 4), (6, 7), (6, 4), (8, 4), (6, 4)]
private abbrev coordinateInput1_72 : LowerPair × Bool × Bool := (([3], [1]), true, false)
private def coordinateCodes1_72 : List (ℕ × ℕ) := [(19, 1), (19, 2), (19, 1), (20, 1)]
private abbrev coordinateInput1_73 : LowerPair × Bool × Bool := (([3], [1]), false, false)
private def coordinateCodes1_73 : List (ℕ × ℕ) := [(21, 4)]
private abbrev coordinateInput1_74 : LowerPair × Bool × Bool := (([3, 1], [1]), true, false)
private def coordinateCodes1_74 : List (ℕ × ℕ) := [(22, 1), (22, 2), (22, 1), (23, 1), (22, 1)]
private abbrev coordinateInput1_75 : LowerPair × Bool × Bool := (([3, 2], [1]), false, false)
private def coordinateCodes1_75 : List (ℕ × ℕ) := [(24, 4), (24, 4), (24, 7), (24, 4), (25, 4)]
private abbrev coordinateInput1_76 : LowerPair × Bool × Bool := (([3, 2], [1]), true, false)
private def coordinateCodes1_76 : List (ℕ × ℕ) := [(20, 1), (20, 2), (20, 1), (26, 1), (20, 1)]
private abbrev coordinateInput1_77 : LowerPair × Bool × Bool := (([3, 1], [1]), false, false)
private def coordinateCodes1_77 : List (ℕ × ℕ) := [(21, 4), (21, 4)]
private abbrev coordinateInput1_78 : LowerPair × Bool × Bool := (([3], [1, 1]), true, true)
private def coordinateCodes1_78 : List (ℕ × ℕ) := [(19, 9), (19, 9), (19, 10), (19, 9), (20, 9)]
private abbrev coordinateInput1_79 : LowerPair × Bool × Bool := (([3], [1, 2]), false, true)
private def coordinateCodes1_79 : List (ℕ × ℕ) := [(21, 11), (21, 11)]
private abbrev coordinateInput1_80 : LowerPair × Bool × Bool := (([3], [1, 2]), true, true)
private def coordinateCodes1_80 : List (ℕ × ℕ) := [(19, 2), (19, 2), (19, 13), (19, 2), (20, 2)]
private abbrev coordinateInput1_81 : LowerPair × Bool × Bool := (([3], [1, 1]), false, true)
private def coordinateCodes1_81 : List (ℕ × ℕ) := [(21, 4), (21, 4)]
private abbrev coordinateInput1_82 : LowerPair × Bool × Bool := (([2], [2]), true, false)
private def coordinateCodes1_82 : List (ℕ × ℕ) := [(0, 0), (0, 3), (0, 0), (3, 0)]
private abbrev coordinateInput1_83 : LowerPair × Bool × Bool := (([2], [2]), false, false)
private def coordinateCodes1_83 : List (ℕ × ℕ) := [(6, 6), (6, 8), (6, 6), (8, 6)]
private abbrev coordinateInput1_84 : LowerPair × Bool × Bool := (([2, 1], [2]), true, false)
private def coordinateCodes1_84 : List (ℕ × ℕ) := [(14, 0), (14, 3), (14, 0), (15, 0), (14, 0)]
private abbrev coordinateInput1_85 : LowerPair × Bool × Bool := (([2, 2], [2]), false, false)
private def coordinateCodes1_85 : List (ℕ × ℕ) := [(16, 6), (16, 6), (16, 8), (16, 6), (17, 6)]
private abbrev coordinateInput1_86 : LowerPair × Bool × Bool := (([2, 2], [2]), true, false)
private def coordinateCodes1_86 : List (ℕ × ℕ) := [(3, 0), (3, 3), (3, 0), (18, 0), (3, 0)]
private abbrev coordinateInput1_87 : LowerPair × Bool × Bool := (([2, 1], [2]), false, false)
private def coordinateCodes1_87 : List (ℕ × ℕ) := [(6, 6), (6, 6), (6, 8), (6, 6), (8, 6)]
private abbrev coordinateInput1_88 : LowerPair × Bool × Bool := (([2], [2, 1]), true, true)
private def coordinateCodes1_88 : List (ℕ × ℕ) := [(0, 14), (0, 14), (0, 15), (0, 14), (3, 14)]
private abbrev coordinateInput1_89 : LowerPair × Bool × Bool := (([2], [2, 2]), false, true)
private def coordinateCodes1_89 : List (ℕ × ℕ) := [(6, 16), (6, 17), (6, 16), (8, 16), (6, 16)]
private abbrev coordinateInput1_90 : LowerPair × Bool × Bool := (([2], [2, 2]), true, true)
private def coordinateCodes1_90 : List (ℕ × ℕ) := [(0, 3), (0, 3), (0, 18), (0, 3), (3, 3)]
private abbrev coordinateInput1_91 : LowerPair × Bool × Bool := (([2], [2, 1]), false, true)
private def coordinateCodes1_91 : List (ℕ × ℕ) := [(6, 6), (6, 8), (6, 6), (8, 6), (6, 6)]
private abbrev coordinateInput1_92 : LowerPair × Bool × Bool := (([2], [3]), true, false)
private def coordinateCodes1_92 : List (ℕ × ℕ) := [(0, 19), (0, 20), (0, 19), (3, 19)]
private abbrev coordinateInput1_93 : LowerPair × Bool × Bool := (([2], [3]), false, false)
private def coordinateCodes1_93 : List (ℕ × ℕ) := [(6, 21)]
private abbrev coordinateInput1_94 : LowerPair × Bool × Bool := (([2, 1], [3]), true, false)
private def coordinateCodes1_94 : List (ℕ × ℕ) := [(14, 19), (14, 20), (14, 19), (15, 19), (14, 19)]
private abbrev coordinateInput1_95 : LowerPair × Bool × Bool := (([2, 2], [3]), false, false)
private def coordinateCodes1_95 : List (ℕ × ℕ) := [(16, 21), (16, 21)]
private abbrev coordinateInput1_96 : LowerPair × Bool × Bool := (([2, 2], [3]), true, false)
private def coordinateCodes1_96 : List (ℕ × ℕ) := [(3, 19), (3, 20), (3, 19), (18, 19), (3, 19)]
private abbrev coordinateInput1_97 : LowerPair × Bool × Bool := (([2, 1], [3]), false, false)
private def coordinateCodes1_97 : List (ℕ × ℕ) := [(6, 21), (6, 21)]
private abbrev coordinateInput1_98 : LowerPair × Bool × Bool := (([2], [3, 1]), true, true)
private def coordinateCodes1_98 : List (ℕ × ℕ) := [(0, 22), (0, 22), (0, 23), (0, 22), (3, 22)]
private abbrev coordinateInput1_99 : LowerPair × Bool × Bool := (([2], [3, 2]), false, true)
private def coordinateCodes1_99 : List (ℕ × ℕ) := [(6, 24), (6, 25), (6, 24), (8, 24), (6, 24)]
private abbrev coordinateInput1_100 : LowerPair × Bool × Bool := (([2], [3, 2]), true, true)
private def coordinateCodes1_100 : List (ℕ × ℕ) := [(0, 20), (0, 20), (0, 26), (0, 20), (3, 20)]
private abbrev coordinateInput1_101 : LowerPair × Bool × Bool := (([2], [3, 1]), false, true)
private def coordinateCodes1_101 : List (ℕ × ℕ) := [(6, 21), (6, 21)]
private abbrev coordinateInput1_102 : LowerPair × Bool × Bool := (([3], [1, 1]), true, false)
private def coordinateCodes1_102 : List (ℕ × ℕ) := [(19, 9), (19, 9), (19, 10), (19, 9), (20, 9)]
private abbrev coordinateInput1_103 : LowerPair × Bool × Bool := (([3], [1, 1]), false, false)
private def coordinateCodes1_103 : List (ℕ × ℕ) := [(21, 4), (21, 4)]
private abbrev coordinateInput1_104 : LowerPair × Bool × Bool := (([3, 1], [1, 1]), true, false)
private def coordinateCodes1_104 : List (ℕ × ℕ) := [(22, 9), (22, 10), (22, 9), (23, 9)]
private abbrev coordinateInput1_105 : LowerPair × Bool × Bool := (([3, 2], [1, 1]), false, false)
private def coordinateCodes1_105 : List (ℕ × ℕ) := [(24, 4), (24, 7), (24, 4), (25, 4)]
private abbrev coordinateInput1_106 : LowerPair × Bool × Bool := (([3, 2], [1, 1]), true, false)
private def coordinateCodes1_106 : List (ℕ × ℕ) := [(20, 9), (20, 10), (20, 9), (26, 9)]
private abbrev coordinateInput1_107 : LowerPair × Bool × Bool := (([3, 1], [1, 1]), false, false)
private def coordinateCodes1_107 : List (ℕ × ℕ) := [(21, 4)]
private abbrev coordinateInput1_108 : LowerPair × Bool × Bool := (([3], [1, 1, 1]), true, true)
private def coordinateCodes1_108 : List (ℕ × ℕ) := [(19, 9), (19, 10), (19, 9), (20, 9)]
private abbrev coordinateInput1_109 : LowerPair × Bool × Bool := (([3], [1, 1, 2]), false, true)
private def coordinateCodes1_109 : List (ℕ × ℕ) := [(21, 7)]
private abbrev coordinateInput1_110 : LowerPair × Bool × Bool := (([3], [1, 1, 2]), true, true)
private def coordinateCodes1_110 : List (ℕ × ℕ) := [(19, 34), (19, 35), (19, 34), (20, 34)]
private abbrev coordinateInput1_111 : LowerPair × Bool × Bool := (([3], [1, 1, 1]), false, true)
private def coordinateCodes1_111 : List (ℕ × ℕ) := [(21, 36)]

private def decodeCoordinate1 (x : ℕ × ℕ) : CertField × CertField :=
  (coordinateFields1[x.1]?.getD ⟨0,0,0,0⟩,coordinateFields1[x.2]?.getD ⟨0,0,0,0⟩)

private theorem hCoordinate1_0 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_0.1 coordinateInput1_0.2.1 coordinateInput1_0.2.2).map Prod.fst = coordinateCodes1_0.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_1 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_1.1 coordinateInput1_1.2.1 coordinateInput1_1.2.2).map Prod.fst = coordinateCodes1_1.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_2 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_2.1 coordinateInput1_2.2.1 coordinateInput1_2.2.2).map Prod.fst = coordinateCodes1_2.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_3 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_3.1 coordinateInput1_3.2.1 coordinateInput1_3.2.2).map Prod.fst = coordinateCodes1_3.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_4 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_4.1 coordinateInput1_4.2.1 coordinateInput1_4.2.2).map Prod.fst = coordinateCodes1_4.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_5 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_5.1 coordinateInput1_5.2.1 coordinateInput1_5.2.2).map Prod.fst = coordinateCodes1_5.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_6 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_6.1 coordinateInput1_6.2.1 coordinateInput1_6.2.2).map Prod.fst = coordinateCodes1_6.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_7 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_7.1 coordinateInput1_7.2.1 coordinateInput1_7.2.2).map Prod.fst = coordinateCodes1_7.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_8 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_8.1 coordinateInput1_8.2.1 coordinateInput1_8.2.2).map Prod.fst = coordinateCodes1_8.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_9 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_9.1 coordinateInput1_9.2.1 coordinateInput1_9.2.2).map Prod.fst = coordinateCodes1_9.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_10 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_10.1 coordinateInput1_10.2.1 coordinateInput1_10.2.2).map Prod.fst = coordinateCodes1_10.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_11 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_11.1 coordinateInput1_11.2.1 coordinateInput1_11.2.2).map Prod.fst = coordinateCodes1_11.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_12 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_12.1 coordinateInput1_12.2.1 coordinateInput1_12.2.2).map Prod.fst = coordinateCodes1_12.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_13 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_13.1 coordinateInput1_13.2.1 coordinateInput1_13.2.2).map Prod.fst = coordinateCodes1_13.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_14 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_14.1 coordinateInput1_14.2.1 coordinateInput1_14.2.2).map Prod.fst = coordinateCodes1_14.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_15 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_15.1 coordinateInput1_15.2.1 coordinateInput1_15.2.2).map Prod.fst = coordinateCodes1_15.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_16 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_16.1 coordinateInput1_16.2.1 coordinateInput1_16.2.2).map Prod.fst = coordinateCodes1_16.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_17 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_17.1 coordinateInput1_17.2.1 coordinateInput1_17.2.2).map Prod.fst = coordinateCodes1_17.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_18 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_18.1 coordinateInput1_18.2.1 coordinateInput1_18.2.2).map Prod.fst = coordinateCodes1_18.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_19 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_19.1 coordinateInput1_19.2.1 coordinateInput1_19.2.2).map Prod.fst = coordinateCodes1_19.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_20 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_20.1 coordinateInput1_20.2.1 coordinateInput1_20.2.2).map Prod.fst = coordinateCodes1_20.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_21 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_21.1 coordinateInput1_21.2.1 coordinateInput1_21.2.2).map Prod.fst = coordinateCodes1_21.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_22 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_22.1 coordinateInput1_22.2.1 coordinateInput1_22.2.2).map Prod.fst = coordinateCodes1_22.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_23 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_23.1 coordinateInput1_23.2.1 coordinateInput1_23.2.2).map Prod.fst = coordinateCodes1_23.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_24 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_24.1 coordinateInput1_24.2.1 coordinateInput1_24.2.2).map Prod.fst = coordinateCodes1_24.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_25 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_25.1 coordinateInput1_25.2.1 coordinateInput1_25.2.2).map Prod.fst = coordinateCodes1_25.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_26 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_26.1 coordinateInput1_26.2.1 coordinateInput1_26.2.2).map Prod.fst = coordinateCodes1_26.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_27 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_27.1 coordinateInput1_27.2.1 coordinateInput1_27.2.2).map Prod.fst = coordinateCodes1_27.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_28 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_28.1 coordinateInput1_28.2.1 coordinateInput1_28.2.2).map Prod.fst = coordinateCodes1_28.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_29 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_29.1 coordinateInput1_29.2.1 coordinateInput1_29.2.2).map Prod.fst = coordinateCodes1_29.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_30 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_30.1 coordinateInput1_30.2.1 coordinateInput1_30.2.2).map Prod.fst = coordinateCodes1_30.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_31 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_31.1 coordinateInput1_31.2.1 coordinateInput1_31.2.2).map Prod.fst = coordinateCodes1_31.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_32 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_32.1 coordinateInput1_32.2.1 coordinateInput1_32.2.2).map Prod.fst = coordinateCodes1_32.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_33 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_33.1 coordinateInput1_33.2.1 coordinateInput1_33.2.2).map Prod.fst = coordinateCodes1_33.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_34 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_34.1 coordinateInput1_34.2.1 coordinateInput1_34.2.2).map Prod.fst = coordinateCodes1_34.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_35 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_35.1 coordinateInput1_35.2.1 coordinateInput1_35.2.2).map Prod.fst = coordinateCodes1_35.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_36 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_36.1 coordinateInput1_36.2.1 coordinateInput1_36.2.2).map Prod.fst = coordinateCodes1_36.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_37 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_37.1 coordinateInput1_37.2.1 coordinateInput1_37.2.2).map Prod.fst = coordinateCodes1_37.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_38 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_38.1 coordinateInput1_38.2.1 coordinateInput1_38.2.2).map Prod.fst = coordinateCodes1_38.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_39 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_39.1 coordinateInput1_39.2.1 coordinateInput1_39.2.2).map Prod.fst = coordinateCodes1_39.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_40 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_40.1 coordinateInput1_40.2.1 coordinateInput1_40.2.2).map Prod.fst = coordinateCodes1_40.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_41 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_41.1 coordinateInput1_41.2.1 coordinateInput1_41.2.2).map Prod.fst = coordinateCodes1_41.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_42 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_42.1 coordinateInput1_42.2.1 coordinateInput1_42.2.2).map Prod.fst = coordinateCodes1_42.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_43 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_43.1 coordinateInput1_43.2.1 coordinateInput1_43.2.2).map Prod.fst = coordinateCodes1_43.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_44 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_44.1 coordinateInput1_44.2.1 coordinateInput1_44.2.2).map Prod.fst = coordinateCodes1_44.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_45 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_45.1 coordinateInput1_45.2.1 coordinateInput1_45.2.2).map Prod.fst = coordinateCodes1_45.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_46 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_46.1 coordinateInput1_46.2.1 coordinateInput1_46.2.2).map Prod.fst = coordinateCodes1_46.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_47 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_47.1 coordinateInput1_47.2.1 coordinateInput1_47.2.2).map Prod.fst = coordinateCodes1_47.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_48 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_48.1 coordinateInput1_48.2.1 coordinateInput1_48.2.2).map Prod.fst = coordinateCodes1_48.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_49 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_49.1 coordinateInput1_49.2.1 coordinateInput1_49.2.2).map Prod.fst = coordinateCodes1_49.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_50 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_50.1 coordinateInput1_50.2.1 coordinateInput1_50.2.2).map Prod.fst = coordinateCodes1_50.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_51 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_51.1 coordinateInput1_51.2.1 coordinateInput1_51.2.2).map Prod.fst = coordinateCodes1_51.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_52 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_52.1 coordinateInput1_52.2.1 coordinateInput1_52.2.2).map Prod.fst = coordinateCodes1_52.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_53 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_53.1 coordinateInput1_53.2.1 coordinateInput1_53.2.2).map Prod.fst = coordinateCodes1_53.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_54 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_54.1 coordinateInput1_54.2.1 coordinateInput1_54.2.2).map Prod.fst = coordinateCodes1_54.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_55 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_55.1 coordinateInput1_55.2.1 coordinateInput1_55.2.2).map Prod.fst = coordinateCodes1_55.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_56 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_56.1 coordinateInput1_56.2.1 coordinateInput1_56.2.2).map Prod.fst = coordinateCodes1_56.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_57 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_57.1 coordinateInput1_57.2.1 coordinateInput1_57.2.2).map Prod.fst = coordinateCodes1_57.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_58 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_58.1 coordinateInput1_58.2.1 coordinateInput1_58.2.2).map Prod.fst = coordinateCodes1_58.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_59 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_59.1 coordinateInput1_59.2.1 coordinateInput1_59.2.2).map Prod.fst = coordinateCodes1_59.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_60 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_60.1 coordinateInput1_60.2.1 coordinateInput1_60.2.2).map Prod.fst = coordinateCodes1_60.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_61 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_61.1 coordinateInput1_61.2.1 coordinateInput1_61.2.2).map Prod.fst = coordinateCodes1_61.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_62 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_62.1 coordinateInput1_62.2.1 coordinateInput1_62.2.2).map Prod.fst = coordinateCodes1_62.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_63 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_63.1 coordinateInput1_63.2.1 coordinateInput1_63.2.2).map Prod.fst = coordinateCodes1_63.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_64 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_64.1 coordinateInput1_64.2.1 coordinateInput1_64.2.2).map Prod.fst = coordinateCodes1_64.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_65 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_65.1 coordinateInput1_65.2.1 coordinateInput1_65.2.2).map Prod.fst = coordinateCodes1_65.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_66 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_66.1 coordinateInput1_66.2.1 coordinateInput1_66.2.2).map Prod.fst = coordinateCodes1_66.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_67 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_67.1 coordinateInput1_67.2.1 coordinateInput1_67.2.2).map Prod.fst = coordinateCodes1_67.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_68 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_68.1 coordinateInput1_68.2.1 coordinateInput1_68.2.2).map Prod.fst = coordinateCodes1_68.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_69 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_69.1 coordinateInput1_69.2.1 coordinateInput1_69.2.2).map Prod.fst = coordinateCodes1_69.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_70 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_70.1 coordinateInput1_70.2.1 coordinateInput1_70.2.2).map Prod.fst = coordinateCodes1_70.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_71 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_71.1 coordinateInput1_71.2.1 coordinateInput1_71.2.2).map Prod.fst = coordinateCodes1_71.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_72 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_72.1 coordinateInput1_72.2.1 coordinateInput1_72.2.2).map Prod.fst = coordinateCodes1_72.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_73 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_73.1 coordinateInput1_73.2.1 coordinateInput1_73.2.2).map Prod.fst = coordinateCodes1_73.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_74 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_74.1 coordinateInput1_74.2.1 coordinateInput1_74.2.2).map Prod.fst = coordinateCodes1_74.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_75 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_75.1 coordinateInput1_75.2.1 coordinateInput1_75.2.2).map Prod.fst = coordinateCodes1_75.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_76 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_76.1 coordinateInput1_76.2.1 coordinateInput1_76.2.2).map Prod.fst = coordinateCodes1_76.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_77 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_77.1 coordinateInput1_77.2.1 coordinateInput1_77.2.2).map Prod.fst = coordinateCodes1_77.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_78 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_78.1 coordinateInput1_78.2.1 coordinateInput1_78.2.2).map Prod.fst = coordinateCodes1_78.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_79 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_79.1 coordinateInput1_79.2.1 coordinateInput1_79.2.2).map Prod.fst = coordinateCodes1_79.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_80 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_80.1 coordinateInput1_80.2.1 coordinateInput1_80.2.2).map Prod.fst = coordinateCodes1_80.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_81 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_81.1 coordinateInput1_81.2.1 coordinateInput1_81.2.2).map Prod.fst = coordinateCodes1_81.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_82 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_82.1 coordinateInput1_82.2.1 coordinateInput1_82.2.2).map Prod.fst = coordinateCodes1_82.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_83 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_83.1 coordinateInput1_83.2.1 coordinateInput1_83.2.2).map Prod.fst = coordinateCodes1_83.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_84 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_84.1 coordinateInput1_84.2.1 coordinateInput1_84.2.2).map Prod.fst = coordinateCodes1_84.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_85 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_85.1 coordinateInput1_85.2.1 coordinateInput1_85.2.2).map Prod.fst = coordinateCodes1_85.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_86 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_86.1 coordinateInput1_86.2.1 coordinateInput1_86.2.2).map Prod.fst = coordinateCodes1_86.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_87 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_87.1 coordinateInput1_87.2.1 coordinateInput1_87.2.2).map Prod.fst = coordinateCodes1_87.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_88 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_88.1 coordinateInput1_88.2.1 coordinateInput1_88.2.2).map Prod.fst = coordinateCodes1_88.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_89 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_89.1 coordinateInput1_89.2.1 coordinateInput1_89.2.2).map Prod.fst = coordinateCodes1_89.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_90 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_90.1 coordinateInput1_90.2.1 coordinateInput1_90.2.2).map Prod.fst = coordinateCodes1_90.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_91 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_91.1 coordinateInput1_91.2.1 coordinateInput1_91.2.2).map Prod.fst = coordinateCodes1_91.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_92 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_92.1 coordinateInput1_92.2.1 coordinateInput1_92.2.2).map Prod.fst = coordinateCodes1_92.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_93 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_93.1 coordinateInput1_93.2.1 coordinateInput1_93.2.2).map Prod.fst = coordinateCodes1_93.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_94 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_94.1 coordinateInput1_94.2.1 coordinateInput1_94.2.2).map Prod.fst = coordinateCodes1_94.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_95 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_95.1 coordinateInput1_95.2.1 coordinateInput1_95.2.2).map Prod.fst = coordinateCodes1_95.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_96 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_96.1 coordinateInput1_96.2.1 coordinateInput1_96.2.2).map Prod.fst = coordinateCodes1_96.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_97 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_97.1 coordinateInput1_97.2.1 coordinateInput1_97.2.2).map Prod.fst = coordinateCodes1_97.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_98 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_98.1 coordinateInput1_98.2.1 coordinateInput1_98.2.2).map Prod.fst = coordinateCodes1_98.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_99 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_99.1 coordinateInput1_99.2.1 coordinateInput1_99.2.2).map Prod.fst = coordinateCodes1_99.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_100 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_100.1 coordinateInput1_100.2.1 coordinateInput1_100.2.2).map Prod.fst = coordinateCodes1_100.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_101 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_101.1 coordinateInput1_101.2.1 coordinateInput1_101.2.2).map Prod.fst = coordinateCodes1_101.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_102 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_102.1 coordinateInput1_102.2.1 coordinateInput1_102.2.2).map Prod.fst = coordinateCodes1_102.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_103 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_103.1 coordinateInput1_103.2.1 coordinateInput1_103.2.2).map Prod.fst = coordinateCodes1_103.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_104 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_104.1 coordinateInput1_104.2.1 coordinateInput1_104.2.2).map Prod.fst = coordinateCodes1_104.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_105 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_105.1 coordinateInput1_105.2.1 coordinateInput1_105.2.2).map Prod.fst = coordinateCodes1_105.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_106 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_106.1 coordinateInput1_106.2.1 coordinateInput1_106.2.2).map Prod.fst = coordinateCodes1_106.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_107 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_107.1 coordinateInput1_107.2.1 coordinateInput1_107.2.2).map Prod.fst = coordinateCodes1_107.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_108 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_108.1 coordinateInput1_108.2.1 coordinateInput1_108.2.2).map Prod.fst = coordinateCodes1_108.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_109 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_109.1 coordinateInput1_109.2.1 coordinateInput1_109.2.2).map Prod.fst = coordinateCodes1_109.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_110 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_110.1 coordinateInput1_110.2.1 coordinateInput1_110.2.2).map Prod.fst = coordinateCodes1_110.map decodeCoordinate1 := by decide +kernel

private theorem hCoordinate1_111 :
    (trunkEndpointCases (trunkCatalog.states 1).context coordinateInput1_111.1 coordinateInput1_111.2.1 coordinateInput1_111.2.2).map Prod.fst = coordinateCodes1_111.map decodeCoordinate1 := by decide +kernel

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

private theorem coverageKeyRecorded_mono (a b : List CoverageKey) (hs : a ⊆ b)
    (plan parent goal : ℕ) (branch : ℤ)
    (h : coverageKeyRecorded a plan parent goal branch) :
    coverageKeyRecorded b plan parent goal branch := by
  obtain ⟨g,hg,h1,h2,h3,h4⟩ := h
  exact ⟨g,hs hg,h1,h2,h3,h4⟩

private def coveragePlanRemainder (plans : List (List CoverageKey)) (tasks : List CoverageTask)
    (parents : ℕ) (remainders : List (List ℕ)) : Prop :=
  ∀ pg ∈ tasks, pg.1 < plans.length ∧
    coverageRemainder (plans[pg.1]?.getD []) [pg] parents remainders

private theorem coveragePlanRemainder_sound (plans : List (List CoverageKey))
    (tasks : List CoverageTask) (parents : ℕ) (remainders : List (List ℕ))
    (h : coveragePlanRemainder plans tasks parents remainders) :
    coverageTable plans.flatten tasks parents := by
  intro pg hpg par hpar
  have hparts := h pg hpg
  have hbound : pg.1 < plans.length := hparts.1
  have hs : plans[pg.1]?.getD [] ⊆ plans.flatten := by
    intro a ha
    have hp : plans[pg.1]?.getD [] = plans[pg.1]'hbound := by
      rw [List.getElem?_eq_getElem hbound]
      rfl
    rw [hp] at ha
    exact List.mem_flatten.mpr ⟨plans[pg.1]'hbound, List.getElem_mem hbound, ha⟩
  have ht := coverageRemainder_sound (plans[pg.1]?.getD []) [pg] parents remainders hparts.2
  rcases ht pg (by simp) par hpar with he | hall
  · exact Or.inl (coverageKeyRecorded_mono _ _ hs _ _ _ _ he)
  · right
    intro gb hgb ba hba
    rcases hall gb hgb ba hba with ha | hr
    · exact Or.inl ha
    · exact Or.inr (coverageKeyRecorded_mono _ _ hs _ _ _ _ hr)
private def kp0 : List ℕ := [0, 50]
private def kp1 : List ℕ := [1, 51]
private def kp2 : List ℕ := [2, 3, 129]
private def kp3 : List ℕ := [4, 29, 54, 79, 104, 109, 114, 119, 124, 125, 126, 127, 128, 150, 151, 152, 153, 175, 176, 177, 178, 200, 201, 202, 203, 230, 231, 232, 233, 235, 236, 237, 238, 240, 241, 242, 243, 245, 246, 247, 248, 250, 251, 252, 253, 275, 276, 277, 278, 300, 301, 302, 303, 325, 326, 327, 328, 355, 356, 357, 358, 360, 361, 362, 363, 365, 366, 367, 368, 370, 371, 372, 373, 375, 376, 377, 378, 400, 401, 402, 403, 425, 426, 427, 428, 450, 451, 452, 453, 480, 481, 482, 483, 485, 486, 487, 488, 490, 491, 492, 493, 495, 496, 497, 498, 500, 501, 502, 503, 525, 526, 527, 528, 550, 551, 552, 553, 575, 576, 577, 578, 605, 606, 607, 608, 610, 611, 612, 613, 615, 616, 617, 618, 620, 621, 622, 623]
private def kp4 : List ℕ := [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604]
private def kp5 : List ℕ := [25]
private def kp6 : List ℕ := [26]
private def kp7 : List ℕ := [27, 154]
private def kp8 : List ℕ := [28]
private def kp9 : List ℕ := [52]
private def kp10 : List ℕ := [53]
private def kp11 : List ℕ := [75]
private def kp12 : List ℕ := [76]
private def kp13 : List ℕ := [77]
private def kp14 : List ℕ := [78]
private def kp15 : List ℕ := [105]
private def kp16 : List ℕ := [106]
private def kp17 : List ℕ := [107]
private def kp18 : List ℕ := [108]
private def kp19 : List ℕ := [110]
private def kp20 : List ℕ := [111]
private def kp21 : List ℕ := [112]
private def kp22 : List ℕ := [113]
private def kp23 : List ℕ := [115]
private def kp24 : List ℕ := [116]
private def kp25 : List ℕ := [117]
private def kp26 : List ℕ := [118]
private def kp27 : List ℕ := [120]
private def kp28 : List ℕ := [121]
private def kp29 : List ℕ := [122]
private def kp30 : List ℕ := [123]
private def kp31 : List ℕ := [179]
private def kp32 : List ℕ := [179, 304]
private def kp33 : List ℕ := [179, 304, 359]
private def kp34 : List ℕ := [204]
private def kp35 : List ℕ := [234]
private def kp36 : List ℕ := [239]
private def kp37 : List ℕ := [244]
private def kp38 : List ℕ := [249]
private def kp39 : List ℕ := [254]
private def kp40 : List ℕ := [279]
private def kp41 : List ℕ := [304]
private def kp42 : List ℕ := [329]
private def kp43 : List ℕ := [359]
private def kp44 : List ℕ := [364, 489, 614]
private def kp45 : List ℕ := [369, 494, 619]
private def kp46 : List ℕ := [374, 499, 624]
private def kp47 : List ℕ := [379]
private def kp48 : List ℕ := [404]
private def kp49 : List ℕ := [429]
private def kp50 : List ℕ := [454]
private def kp51 : List ℕ := [484]
private def kp52 : List ℕ := [504]
private def kp53 : List ℕ := [529]
private def kp54 : List ℕ := [554]
private def kp55 : List ℕ := [579]
private def kp56 : List ℕ := [609]
private def kp57 : List ℕ := [0, 25, 50, 75, 105, 110]
private def kp58 : List ℕ := [1, 26, 51, 76, 106, 111]
private def kp59 : List ℕ := [2, 3, 129, 254, 379, 504]
private def kp60 : List ℕ := [4, 29, 54, 79, 109, 114, 119, 124, 125, 126, 127, 128, 150, 151, 152, 153, 175, 176, 177, 178, 200, 201, 202, 203, 230, 231, 232, 233, 235, 236, 237, 238, 240, 241, 242, 243, 245, 246, 247, 248, 250, 251, 252, 253, 275, 276, 277, 278, 300, 301, 302, 303, 325, 326, 327, 328, 355, 356, 357, 358, 360, 361, 362, 363, 365, 366, 367, 368, 370, 371, 372, 373, 375, 376, 377, 378, 400, 401, 402, 403, 425, 426, 427, 428, 450, 451, 452, 453, 480, 481, 482, 483, 485, 486, 487, 488, 490, 491, 492, 493, 495, 496, 497, 498, 500, 501, 502, 503, 525, 526, 527, 528, 550, 551, 552, 553, 575, 576, 577, 578, 605, 606, 607, 608, 610, 611, 612, 613, 615, 616, 617, 618, 620, 621, 622, 623]
private def kp61 : List ℕ := [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604]
private def kp62 : List ℕ := [27, 154, 279, 404, 529]
private def kp63 : List ℕ := [28, 53, 78, 108, 113]
private def kp64 : List ℕ := [52, 77, 107, 112]
private def kp65 : List ℕ := [179, 234, 239]
private def kp66 : List ℕ := [204, 329, 454, 579]
private def kp67 : List ℕ := [304, 429, 554]
private def kp68 : List ℕ := [359, 364]
private def kp69 : List ℕ := [369]
private def kp70 : List ℕ := [374]
private def kp71 : List ℕ := [484, 489]
private def kp72 : List ℕ := [494]
private def kp73 : List ℕ := [499]
private def kp74 : List ℕ := [609, 614]
private def kp75 : List ℕ := [619]
private def kp76 : List ℕ := [624]
private def kp77 : List ℕ := [0, 25, 50, 75, 105]
private def kp78 : List ℕ := [1, 26, 51, 76, 106]
private def kp79 : List ℕ := [2, 3, 129, 254]
private def kp80 : List ℕ := [27, 154, 279]
private def kp81 : List ℕ := [28, 53, 78, 108]
private def kp82 : List ℕ := [52, 77, 107]
private def kp83 : List ℕ := [179, 234]
private def kp84 : List ℕ := [204, 329]
private def kp85 : List ℕ := [304, 359, 484, 489, 609]
private def kp86 : List ℕ := [304, 359]
private def kp87 : List ℕ := [359, 484, 489, 609]
private def kp88 : List ℕ := [359, 484, 609]
private def kp89 : List ℕ := [364]
private def kp90 : List ℕ := [489]
private def kp91 : List ℕ := [614]
private def kp92 : List ℕ := [489, 499]
private def kp93 : List ℕ := [0, 25, 50, 75, 105, 110, 120]
private def kp94 : List ℕ := [1, 26, 51, 76, 106, 111, 121]
private def kp95 : List ℕ := [28, 53, 78, 108, 113, 123]
private def kp96 : List ℕ := [52, 77, 107, 112, 122]
private def kp97 : List ℕ := [179, 234, 239, 249]
private def kp98 : List ℕ := [359, 364, 374]
private def kp99 : List ℕ := [609, 614, 624]
private def kb0 : List ℤ := [-1]
private def kb1 : List ℤ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
private def kb2 : List ℤ := [0, 1, 2, 3]
private def kb3 : List ℤ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
private def kb4 : List ℤ := [8, 10, 11, 16, 17, 18]
private def kb5 : List ℤ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
private def kb6 : List ℤ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
private def kb7 : List ℤ := [12, 13, 14, 15]
private def kb8 : List ℤ := [0]
private def kb9 : List ℤ := [0, 2, 3]
private def kb10 : List ℤ := [0, 1, 2, 3, 4, 5, 6, 7]
private def pk0 : List CoverageKey := [(0,kp0,0,kb0),(0,kp1,0,kb0),(0,kp2,0,kb0),(0,kp3,0,kb0),(0,kp4,0,kb0),(0,kp5,0,kb0),(0,kp6,0,kb0),(0,kp7,0,kb0),(0,kp8,0,kb0),(0,kp9,0,kb0),(0,kp10,0,kb0),(0,kp11,0,kb0),(0,kp12,0,kb0),(0,kp13,0,kb0),(0,kp14,0,kb0),(0,kp15,0,kb0),(0,kp16,0,kb0),(0,kp17,0,kb0),(0,kp18,0,kb0),(0,kp19,0,kb0),(0,kp20,0,kb0),(0,kp21,0,kb0),(0,kp22,0,kb0),(0,kp23,0,kb0),(0,kp24,0,kb0),(0,kp25,0,kb0),(0,kp26,0,kb0),(0,kp27,0,kb0),(0,kp28,0,kb0),(0,kp29,0,kb0),(0,kp30,0,kb0),(0,kp31,2,kb1),(0,kp32,5,kb1),(0,kp33,7,kb1),(0,kp31,10,kb1),(0,kp31,12,kb1),(0,kp31,15,kb2),(0,kp31,17,kb3),(0,kp31,19,kb3),(0,kp32,20,kb4),(0,kp34,0,kb0),(0,kp35,0,kb0),(0,kp36,0,kb0),(0,kp37,0,kb0),(0,kp38,0,kb0),(0,kp39,0,kb0),(0,kp40,0,kb0),(0,kp41,2,kb1),(0,kp41,10,kb1),(0,kp41,12,kb1),(0,kp41,15,kb2),(0,kp41,17,kb3),(0,kp41,19,kb3),(0,kp42,0,kb0),(0,kp43,2,kb1),(0,kp43,5,kb1),(0,kp43,10,kb1),(0,kp43,12,kb1),(0,kp43,15,kb2),(0,kp43,17,kb3),(0,kp43,19,kb3),(0,kp43,20,kb4),(0,kp44,0,kb0),(0,kp45,0,kb0),(0,kp46,0,kb0),(0,kp47,0,kb0),(0,kp48,0,kb0),(0,kp49,0,kb0),(0,kp50,0,kb0),(0,kp51,0,kb0),(0,kp52,0,kb0),(0,kp53,0,kb0),(0,kp54,0,kb0),(0,kp55,0,kb0),(0,kp56,0,kb0)]
private def pk1 : List CoverageKey := [(1,kp57,0,kb0),(1,kp58,0,kb0),(1,kp59,0,kb0),(1,kp60,0,kb0),(1,kp61,0,kb0),(1,kp62,0,kb0),(1,kp63,0,kb0),(1,kp64,0,kb0),(1,kp23,0,kb0),(1,kp24,0,kb0),(1,kp25,0,kb0),(1,kp26,0,kb0),(1,kp27,0,kb0),(1,kp28,0,kb0),(1,kp29,0,kb0),(1,kp30,0,kb0),(1,kp65,0,kb0),(1,kp66,0,kb0),(1,kp37,0,kb0),(1,kp38,0,kb0),(1,kp67,0,kb0),(1,kp68,0,kb0),(1,kp69,0,kb0),(1,kp70,0,kb0),(1,kp71,0,kb0),(1,kp72,0,kb0),(1,kp73,0,kb0),(1,kp74,0,kb0),(1,kp75,0,kb0),(1,kp76,0,kb0)]
private def pk2 : List CoverageKey := [(2,kp77,0,kb0),(2,kp78,0,kb0),(2,kp79,0,kb0),(2,kp60,0,kb0),(2,kp61,0,kb0),(2,kp80,0,kb0),(2,kp81,0,kb0),(2,kp82,0,kb0),(2,kp19,0,kb0),(2,kp20,0,kb0),(2,kp21,0,kb0),(2,kp22,0,kb0),(2,kp23,0,kb0),(2,kp24,0,kb0),(2,kp25,0,kb0),(2,kp26,0,kb0),(2,kp27,0,kb0),(2,kp28,0,kb0),(2,kp29,0,kb0),(2,kp30,0,kb0),(2,kp83,0,kb0),(2,kp84,0,kb0),(2,kp36,0,kb0),(2,kp37,0,kb0),(2,kp38,0,kb0),(2,kp41,2,kb1),(2,kp41,5,kb1),(2,kp85,7,kb1),(2,kp41,10,kb1),(2,kp86,12,kb3),(2,kp41,14,kb5),(2,kp86,18,kb5),(2,kp41,20,kb5),(2,kp86,22,kb5),(2,kp41,24,kb5),(2,kp41,27,kb3),(2,kp41,29,kb6),(2,kp85,30,kb7),(2,kp41,31,kb8),(2,kp41,32,kb4),(2,kp87,2,kb1),(2,kp43,5,kb1),(2,kp43,10,kb1),(2,kp43,14,kb5),(2,kp43,20,kb5),(2,kp43,24,kb5),(2,kp43,27,kb3),(2,kp43,29,kb6),(2,kp43,31,kb8),(2,kp88,32,kb4),(2,kp89,0,kb0),(2,kp69,0,kb0),(2,kp70,0,kb0),(2,kp47,0,kb0),(2,kp48,0,kb0),(2,kp49,0,kb0),(2,kp50,0,kb0),(2,kp51,5,kb1),(2,kp51,10,kb1),(2,kp51,12,kb3),(2,kp51,14,kb5),(2,kp51,18,kb5),(2,kp51,20,kb5),(2,kp51,22,kb5),(2,kp51,24,kb5),(2,kp71,27,kb3),(2,kp51,29,kb6),(2,kp71,31,kb8),(2,kp90,5,kb1),(2,kp90,10,kb1),(2,kp90,12,kb3),(2,kp90,14,kb5),(2,kp90,18,kb5),(2,kp90,20,kb5),(2,kp90,22,kb5),(2,kp90,24,kb5),(2,kp90,29,kb6),(2,kp90,32,kb4),(2,kp72,0,kb0),(2,kp73,0,kb0),(2,kp52,0,kb0),(2,kp53,0,kb0),(2,kp54,0,kb0),(2,kp55,0,kb0),(2,kp56,5,kb1),(2,kp56,10,kb1),(2,kp56,12,kb3),(2,kp56,14,kb5),(2,kp56,18,kb5),(2,kp56,20,kb5),(2,kp56,22,kb5),(2,kp56,24,kb5),(2,kp56,27,kb3),(2,kp56,29,kb6),(2,kp56,31,kb8),(2,kp91,0,kb0),(2,kp75,0,kb0),(2,kp76,0,kb0)]
private def pk3 : List CoverageKey := [(3,kp57,0,kb0),(3,kp58,0,kb0),(3,kp59,0,kb0),(3,kp60,0,kb0),(3,kp61,0,kb0),(3,kp62,0,kb0),(3,kp63,0,kb0),(3,kp64,0,kb0),(3,kp23,0,kb0),(3,kp24,0,kb0),(3,kp25,0,kb0),(3,kp26,0,kb0),(3,kp27,0,kb0),(3,kp28,0,kb0),(3,kp29,0,kb0),(3,kp30,0,kb0),(3,kp65,0,kb0),(3,kp66,0,kb0),(3,kp37,0,kb0),(3,kp38,0,kb0),(3,kp67,0,kb0),(3,kp68,0,kb0),(3,kp69,0,kb0),(3,kp70,0,kb0),(3,kp51,0,kb0),(3,kp92,2,kb1),(3,kp90,5,kb1),(3,kp92,7,kb3),(3,kp90,9,kb3),(3,kp90,12,kb3),(3,kp90,14,kb5),(3,kp90,17,kb3),(3,kp90,19,kb3),(3,kp90,22,kb5),(3,kp90,24,kb3),(3,kp90,27,kb3),(3,kp90,29,kb5),(3,kp92,32,kb6),(3,kp90,34,kb1),(3,kp90,35,kb1),(3,kp90,36,kb2),(3,kp90,38,kb1),(3,kp90,39,kb2),(3,kp90,40,kb2),(3,kp90,41,kb4),(3,kp92,42,kb9),(3,kp72,0,kb0),(3,kp73,5,kb1),(3,kp73,9,kb3),(3,kp73,12,kb3),(3,kp73,14,kb5),(3,kp73,17,kb3),(3,kp73,19,kb3),(3,kp73,22,kb5),(3,kp73,24,kb3),(3,kp73,27,kb3),(3,kp73,29,kb5),(3,kp73,34,kb1),(3,kp73,35,kb1),(3,kp73,36,kb2),(3,kp73,38,kb1),(3,kp73,39,kb2),(3,kp73,40,kb2),(3,kp73,41,kb4),(3,kp74,0,kb0),(3,kp75,0,kb0),(3,kp76,0,kb0)]
private def pk4 : List CoverageKey := [(4,kp57,0,kb0),(4,kp58,0,kb0),(4,kp59,0,kb0),(4,kp60,0,kb0),(4,kp61,0,kb0),(4,kp62,0,kb0),(4,kp63,0,kb0),(4,kp64,0,kb0),(4,kp23,0,kb0),(4,kp24,0,kb0),(4,kp25,0,kb0),(4,kp26,0,kb0),(4,kp27,0,kb0),(4,kp28,0,kb0),(4,kp29,0,kb0),(4,kp30,0,kb0),(4,kp65,0,kb0),(4,kp66,0,kb0),(4,kp37,0,kb0),(4,kp38,0,kb0),(4,kp67,0,kb0),(4,kp68,0,kb0),(4,kp69,0,kb0),(4,kp70,0,kb0),(4,kp71,2,kb1),(4,kp51,5,kb1),(4,kp71,7,kb3),(4,kp51,9,kb3),(4,kp71,12,kb3),(4,kp51,14,kb5),(4,kp71,17,kb3),(4,kp51,19,kb3),(4,kp71,22,kb5),(4,kp51,24,kb3),(4,kp71,27,kb3),(4,kp51,29,kb5),(4,kp71,33,kb5),(4,kp51,35,kb5),(4,kp71,37,kb5),(4,kp51,39,kb5),(4,kp71,42,kb6),(4,kp71,44,kb1),(4,kp71,45,kb1),(4,kp51,46,kb2),(4,kp51,48,kb1),(4,kp51,49,kb2),(4,kp71,50,kb2),(4,kp71,51,kb7),(4,kp51,52,kb8),(4,kp51,53,kb4),(4,kp90,5,kb1),(4,kp90,9,kb3),(4,kp90,14,kb5),(4,kp90,19,kb3),(4,kp90,24,kb3),(4,kp90,29,kb5),(4,kp90,35,kb5),(4,kp90,39,kb5),(4,kp90,46,kb2),(4,kp90,48,kb1),(4,kp90,49,kb2),(4,kp90,52,kb8),(4,kp90,53,kb4),(4,kp72,0,kb0),(4,kp73,0,kb0),(4,kp74,0,kb0),(4,kp75,0,kb0),(4,kp76,0,kb0)]
private def pk5 : List CoverageKey := [(5,kp93,0,kb0),(5,kp94,0,kb0),(5,kp59,0,kb0),(5,kp60,0,kb0),(5,kp61,0,kb0),(5,kp62,0,kb0),(5,kp95,0,kb0),(5,kp96,0,kb0),(5,kp23,0,kb0),(5,kp24,0,kb0),(5,kp25,0,kb0),(5,kp26,0,kb0),(5,kp97,0,kb0),(5,kp66,0,kb0),(5,kp37,0,kb0),(5,kp67,0,kb0),(5,kp98,0,kb0),(5,kp69,0,kb0),(5,kp51,0,kb0),(5,kp92,2,kb1),(5,kp90,5,kb1),(5,kp92,7,kb3),(5,kp90,9,kb3),(5,kp92,12,kb1),(5,kp90,15,kb2),(5,kp92,17,kb3),(5,kp90,19,kb3),(5,kp92,22,kb5),(5,kp90,24,kb3),(5,kp92,27,kb3),(5,kp90,29,kb5),(5,kp92,32,kb6),(5,kp90,34,kb6),(5,kp92,35,kb6),(5,kp90,36,kb10),(5,kp90,38,kb1),(5,kp90,39,kb2),(5,kp92,40,kb2),(5,kp90,41,kb4),(5,kp92,42,kb9),(5,kp72,0,kb0),(5,kp73,5,kb1),(5,kp73,9,kb3),(5,kp73,15,kb2),(5,kp73,19,kb3),(5,kp73,24,kb3),(5,kp73,29,kb5),(5,kp73,34,kb6),(5,kp73,36,kb10),(5,kp73,38,kb1),(5,kp73,39,kb2),(5,kp73,41,kb4),(5,kp99,0,kb0),(5,kp75,0,kb0)]
private def pk6 : List CoverageKey := [(6,kp93,0,kb0),(6,kp94,0,kb0),(6,kp59,0,kb0),(6,kp60,0,kb0),(6,kp61,0,kb0),(6,kp62,0,kb0),(6,kp95,0,kb0),(6,kp96,0,kb0),(6,kp23,0,kb0),(6,kp24,0,kb0),(6,kp25,0,kb0),(6,kp26,0,kb0),(6,kp97,0,kb0),(6,kp66,0,kb0),(6,kp37,0,kb0),(6,kp67,0,kb0),(6,kp98,0,kb0),(6,kp69,0,kb0),(6,kp51,0,kb0),(6,kp92,0,kb0),(6,kp72,0,kb0),(6,kp99,0,kb0),(6,kp75,0,kb0)]
private def checkedPlanKeys : List (List CoverageKey) := [pk0,pk1,pk2,pk3,pk4,pk5,pk6]
private def checkedKeys : List CoverageKey := checkedPlanKeys.flatten
private def checkedTasks : List CoverageTask := [(0,[(1, (List.replicate 25 true).zipIdx.map Prod.swap),(2, (List.replicate 16 false).zipIdx.map Prod.swap),(3, (List.replicate 16 true).zipIdx.map Prod.swap),(4, (List.replicate 16 true).zipIdx.map Prod.swap),(5, (List.replicate 16 false).zipIdx.map Prod.swap),(6, (List.replicate 25 true).zipIdx.map Prod.swap),(7, (List.replicate 16 false).zipIdx.map Prod.swap),(8, (List.replicate 16 true).zipIdx.map Prod.swap),(9, (List.replicate 16 true).zipIdx.map Prod.swap),(10, (List.replicate 16 false).zipIdx.map Prod.swap),(11, (List.replicate 10 true).zipIdx.map Prod.swap),(12, (List.replicate 16 false).zipIdx.map Prod.swap),(13, (List.replicate 4 true).zipIdx.map Prod.swap),(14, (List.replicate 4 true).zipIdx.map Prod.swap),(15, (List.replicate 4 false).zipIdx.map Prod.swap),(16, (List.replicate 25 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 10 true).zipIdx.map Prod.swap),(19, (List.replicate 25 false).zipIdx.map Prod.swap),(20, [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true].zipIdx.map Prod.swap),(21, (List.replicate 8 true).zipIdx.map Prod.swap)]),(1,[(1, (List.replicate 25 true).zipIdx.map Prod.swap),(2, (List.replicate 16 false).zipIdx.map Prod.swap),(3, (List.replicate 16 true).zipIdx.map Prod.swap),(4, (List.replicate 16 true).zipIdx.map Prod.swap),(5, (List.replicate 16 false).zipIdx.map Prod.swap),(6, (List.replicate 25 true).zipIdx.map Prod.swap),(7, (List.replicate 16 false).zipIdx.map Prod.swap),(8, (List.replicate 16 true).zipIdx.map Prod.swap),(9, (List.replicate 16 true).zipIdx.map Prod.swap),(10, (List.replicate 16 false).zipIdx.map Prod.swap),(11, (List.replicate 4 true).zipIdx.map Prod.swap),(12, (List.replicate 25 false).zipIdx.map Prod.swap),(13, (List.replicate 10 true).zipIdx.map Prod.swap),(14, (List.replicate 10 false).zipIdx.map Prod.swap),(15, (List.replicate 10 true).zipIdx.map Prod.swap),(16, (List.replicate 25 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 5 true).zipIdx.map Prod.swap),(19, (List.replicate 20 false).zipIdx.map Prod.swap),(20, [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true].zipIdx.map Prod.swap),(21, [false, true, false, false].zipIdx.map Prod.swap)]),(2,[(1, (List.replicate 25 true).zipIdx.map Prod.swap),(2, (List.replicate 16 false).zipIdx.map Prod.swap),(3, (List.replicate 16 true).zipIdx.map Prod.swap),(4, (List.replicate 16 true).zipIdx.map Prod.swap),(5, (List.replicate 16 false).zipIdx.map Prod.swap),(6, (List.replicate 25 true).zipIdx.map Prod.swap),(7, (List.replicate 16 false).zipIdx.map Prod.swap),(8, (List.replicate 16 true).zipIdx.map Prod.swap),(9, (List.replicate 16 true).zipIdx.map Prod.swap),(10, (List.replicate 16 false).zipIdx.map Prod.swap),(11, (List.replicate 4 true).zipIdx.map Prod.swap),(12, (List.replicate 25 false).zipIdx.map Prod.swap),(13, (List.replicate 10 true).zipIdx.map Prod.swap),(14, (List.replicate 10 false).zipIdx.map Prod.swap),(15, (List.replicate 10 true).zipIdx.map Prod.swap),(16, (List.replicate 4 true).zipIdx.map Prod.swap),(17, (List.replicate 10 true).zipIdx.map Prod.swap),(18, (List.replicate 10 false).zipIdx.map Prod.swap),(19, (List.replicate 10 true).zipIdx.map Prod.swap),(20, (List.replicate 10 false).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 10 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 25 true).zipIdx.map Prod.swap),(27, (List.replicate 25 false).zipIdx.map Prod.swap),(28, (List.replicate 5 true).zipIdx.map Prod.swap),(29, (List.replicate 20 false).zipIdx.map Prod.swap),(30, [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false].zipIdx.map Prod.swap),(31, (List.replicate 1 false).zipIdx.map Prod.swap),(32, [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true].zipIdx.map Prod.swap),(33, (List.replicate 4 true).zipIdx.map Prod.swap)]),(3,[(1, (List.replicate 25 true).zipIdx.map Prod.swap),(2, (List.replicate 16 false).zipIdx.map Prod.swap),(3, (List.replicate 16 true).zipIdx.map Prod.swap),(4, (List.replicate 16 true).zipIdx.map Prod.swap),(5, (List.replicate 16 false).zipIdx.map Prod.swap),(6, (List.replicate 16 true).zipIdx.map Prod.swap),(7, (List.replicate 25 false).zipIdx.map Prod.swap),(8, (List.replicate 25 true).zipIdx.map Prod.swap),(9, (List.replicate 25 false).zipIdx.map Prod.swap),(10, (List.replicate 25 true).zipIdx.map Prod.swap),(11, (List.replicate 4 true).zipIdx.map Prod.swap),(12, (List.replicate 25 false).zipIdx.map Prod.swap),(13, (List.replicate 10 true).zipIdx.map Prod.swap),(14, (List.replicate 10 false).zipIdx.map Prod.swap),(15, (List.replicate 10 true).zipIdx.map Prod.swap),(16, (List.replicate 16 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 25 true).zipIdx.map Prod.swap),(19, (List.replicate 25 false).zipIdx.map Prod.swap),(20, (List.replicate 25 true).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 25 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 4 true).zipIdx.map Prod.swap),(27, (List.replicate 25 false).zipIdx.map Prod.swap),(28, (List.replicate 10 true).zipIdx.map Prod.swap),(29, (List.replicate 10 false).zipIdx.map Prod.swap),(30, (List.replicate 10 true).zipIdx.map Prod.swap),(31, (List.replicate 20 true).zipIdx.map Prod.swap),(32, (List.replicate 20 false).zipIdx.map Prod.swap),(33, (List.replicate 4 true).zipIdx.map Prod.swap),(34, (List.replicate 16 false).zipIdx.map Prod.swap),(35, (List.replicate 16 false).zipIdx.map Prod.swap),(36, (List.replicate 4 false).zipIdx.map Prod.swap),(37, (List.replicate 4 true).zipIdx.map Prod.swap),(38, (List.replicate 16 false).zipIdx.map Prod.swap),(39, (List.replicate 4 false).zipIdx.map Prod.swap),(40, (List.replicate 4 false).zipIdx.map Prod.swap),(41, [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true].zipIdx.map Prod.swap),(42, [false, true, false, false].zipIdx.map Prod.swap)]),(4,[(1, (List.replicate 25 true).zipIdx.map Prod.swap),(2, (List.replicate 16 false).zipIdx.map Prod.swap),(3, (List.replicate 16 true).zipIdx.map Prod.swap),(4, (List.replicate 16 true).zipIdx.map Prod.swap),(5, (List.replicate 16 false).zipIdx.map Prod.swap),(6, (List.replicate 16 true).zipIdx.map Prod.swap),(7, (List.replicate 25 false).zipIdx.map Prod.swap),(8, (List.replicate 25 true).zipIdx.map Prod.swap),(9, (List.replicate 25 false).zipIdx.map Prod.swap),(10, (List.replicate 25 true).zipIdx.map Prod.swap),(11, (List.replicate 4 true).zipIdx.map Prod.swap),(12, (List.replicate 25 false).zipIdx.map Prod.swap),(13, (List.replicate 10 true).zipIdx.map Prod.swap),(14, (List.replicate 10 false).zipIdx.map Prod.swap),(15, (List.replicate 10 true).zipIdx.map Prod.swap),(16, (List.replicate 16 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 25 true).zipIdx.map Prod.swap),(19, (List.replicate 25 false).zipIdx.map Prod.swap),(20, (List.replicate 25 true).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 25 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 4 true).zipIdx.map Prod.swap),(27, (List.replicate 25 false).zipIdx.map Prod.swap),(28, (List.replicate 10 true).zipIdx.map Prod.swap),(29, (List.replicate 10 false).zipIdx.map Prod.swap),(30, (List.replicate 10 true).zipIdx.map Prod.swap),(31, (List.replicate 4 true).zipIdx.map Prod.swap),(32, (List.replicate 10 true).zipIdx.map Prod.swap),(33, (List.replicate 10 false).zipIdx.map Prod.swap),(34, (List.replicate 10 true).zipIdx.map Prod.swap),(35, (List.replicate 10 false).zipIdx.map Prod.swap),(36, (List.replicate 4 true).zipIdx.map Prod.swap),(37, (List.replicate 10 false).zipIdx.map Prod.swap),(38, (List.replicate 10 true).zipIdx.map Prod.swap),(39, (List.replicate 10 false).zipIdx.map Prod.swap),(40, (List.replicate 10 true).zipIdx.map Prod.swap),(41, (List.replicate 20 true).zipIdx.map Prod.swap),(42, (List.replicate 20 false).zipIdx.map Prod.swap),(43, (List.replicate 4 true).zipIdx.map Prod.swap),(44, (List.replicate 16 false).zipIdx.map Prod.swap),(45, (List.replicate 16 false).zipIdx.map Prod.swap),(46, (List.replicate 4 false).zipIdx.map Prod.swap),(47, (List.replicate 4 true).zipIdx.map Prod.swap),(48, (List.replicate 16 false).zipIdx.map Prod.swap),(49, (List.replicate 4 false).zipIdx.map Prod.swap),(50, (List.replicate 4 false).zipIdx.map Prod.swap),(51, [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false].zipIdx.map Prod.swap),(52, (List.replicate 1 false).zipIdx.map Prod.swap),(53, [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true].zipIdx.map Prod.swap),(54, (List.replicate 4 true).zipIdx.map Prod.swap)]),(5,[(1, (List.replicate 25 true).zipIdx.map Prod.swap),(2, (List.replicate 16 false).zipIdx.map Prod.swap),(3, (List.replicate 16 true).zipIdx.map Prod.swap),(4, (List.replicate 16 true).zipIdx.map Prod.swap),(5, (List.replicate 16 false).zipIdx.map Prod.swap),(6, (List.replicate 16 true).zipIdx.map Prod.swap),(7, (List.replicate 25 false).zipIdx.map Prod.swap),(8, (List.replicate 25 true).zipIdx.map Prod.swap),(9, (List.replicate 25 false).zipIdx.map Prod.swap),(10, (List.replicate 25 true).zipIdx.map Prod.swap),(11, (List.replicate 10 true).zipIdx.map Prod.swap),(12, (List.replicate 16 false).zipIdx.map Prod.swap),(13, (List.replicate 4 true).zipIdx.map Prod.swap),(14, (List.replicate 4 true).zipIdx.map Prod.swap),(15, (List.replicate 4 false).zipIdx.map Prod.swap),(16, (List.replicate 16 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 25 true).zipIdx.map Prod.swap),(19, (List.replicate 25 false).zipIdx.map Prod.swap),(20, (List.replicate 25 true).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 25 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 4 true).zipIdx.map Prod.swap),(27, (List.replicate 25 false).zipIdx.map Prod.swap),(28, (List.replicate 10 true).zipIdx.map Prod.swap),(29, (List.replicate 10 false).zipIdx.map Prod.swap),(30, (List.replicate 10 true).zipIdx.map Prod.swap),(31, (List.replicate 20 true).zipIdx.map Prod.swap),(32, (List.replicate 20 false).zipIdx.map Prod.swap),(33, (List.replicate 8 true).zipIdx.map Prod.swap),(34, (List.replicate 20 false).zipIdx.map Prod.swap),(35, (List.replicate 20 false).zipIdx.map Prod.swap),(36, (List.replicate 8 false).zipIdx.map Prod.swap),(37, (List.replicate 4 true).zipIdx.map Prod.swap),(38, (List.replicate 16 false).zipIdx.map Prod.swap),(39, (List.replicate 4 false).zipIdx.map Prod.swap),(40, (List.replicate 4 false).zipIdx.map Prod.swap),(41, [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true].zipIdx.map Prod.swap),(42, [false, true, false, false].zipIdx.map Prod.swap)]),(6,[(1, (List.replicate 25 true).zipIdx.map Prod.swap),(2, (List.replicate 16 false).zipIdx.map Prod.swap),(3, (List.replicate 16 true).zipIdx.map Prod.swap),(4, (List.replicate 16 true).zipIdx.map Prod.swap),(5, (List.replicate 16 false).zipIdx.map Prod.swap),(6, (List.replicate 16 true).zipIdx.map Prod.swap),(7, (List.replicate 25 false).zipIdx.map Prod.swap),(8, (List.replicate 25 true).zipIdx.map Prod.swap),(9, (List.replicate 25 false).zipIdx.map Prod.swap),(10, (List.replicate 25 true).zipIdx.map Prod.swap),(11, (List.replicate 10 true).zipIdx.map Prod.swap),(12, (List.replicate 16 false).zipIdx.map Prod.swap),(13, (List.replicate 4 true).zipIdx.map Prod.swap),(14, (List.replicate 4 true).zipIdx.map Prod.swap),(15, (List.replicate 4 false).zipIdx.map Prod.swap),(16, (List.replicate 16 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 25 true).zipIdx.map Prod.swap),(19, (List.replicate 25 false).zipIdx.map Prod.swap),(20, (List.replicate 25 true).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 25 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 4 true).zipIdx.map Prod.swap),(27, (List.replicate 25 false).zipIdx.map Prod.swap),(28, (List.replicate 10 true).zipIdx.map Prod.swap),(29, (List.replicate 10 false).zipIdx.map Prod.swap),(30, (List.replicate 10 true).zipIdx.map Prod.swap),(31, (List.replicate 4 true).zipIdx.map Prod.swap),(32, (List.replicate 10 true).zipIdx.map Prod.swap),(33, (List.replicate 10 false).zipIdx.map Prod.swap),(34, (List.replicate 10 true).zipIdx.map Prod.swap),(35, (List.replicate 10 false).zipIdx.map Prod.swap),(36, (List.replicate 4 true).zipIdx.map Prod.swap),(37, (List.replicate 10 false).zipIdx.map Prod.swap),(38, (List.replicate 10 true).zipIdx.map Prod.swap),(39, (List.replicate 10 false).zipIdx.map Prod.swap),(40, (List.replicate 10 true).zipIdx.map Prod.swap),(41, (List.replicate 20 true).zipIdx.map Prod.swap),(42, (List.replicate 20 false).zipIdx.map Prod.swap),(43, (List.replicate 8 true).zipIdx.map Prod.swap),(44, (List.replicate 20 false).zipIdx.map Prod.swap),(45, (List.replicate 20 false).zipIdx.map Prod.swap),(46, (List.replicate 8 false).zipIdx.map Prod.swap),(47, (List.replicate 4 true).zipIdx.map Prod.swap),(48, (List.replicate 16 false).zipIdx.map Prod.swap),(49, (List.replicate 4 false).zipIdx.map Prod.swap),(50, (List.replicate 4 false).zipIdx.map Prod.swap),(51, [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false].zipIdx.map Prod.swap),(52, (List.replicate 1 false).zipIdx.map Prod.swap),(53, [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true].zipIdx.map Prod.swap),(54, (List.replicate 4 true).zipIdx.map Prod.swap)])]
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
private abbrev specAt1 (pi goal : ℕ) : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 1) pi))[goal-1]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private abbrev cSpec1_0_1 := specAt1 0 1
private theorem cFlags1_0_1 : automaticFlags (trunkCatalog.states 1).context cSpec1_0_1 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_2 coordinateInput1_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_2 hCoordinate1_1]
  decide +kernel
private abbrev cSpec1_0_2 := specAt1 0 2
private theorem cFlags1_0_2 : automaticFlags (trunkCatalog.states 1).context cSpec1_0_2 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_4 coordinateInput1_5 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_4 hCoordinate1_5]
  decide +kernel
private abbrev cSpec1_0_3 := specAt1 0 3
private theorem cFlags1_0_3 : automaticFlags (trunkCatalog.states 1).context cSpec1_0_3 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_6 coordinateInput1_7 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_6 hCoordinate1_7]
  decide +kernel
private abbrev cSpec1_0_4 := specAt1 0 4
private theorem cFlags1_0_4 : automaticFlags (trunkCatalog.states 1).context cSpec1_0_4 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_8 coordinateInput1_9 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_8 hCoordinate1_9]
  decide +kernel
private abbrev cSpec1_0_5 := specAt1 0 5
private theorem cFlags1_0_5 : automaticFlags (trunkCatalog.states 1).context cSpec1_0_5 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_10 coordinateInput1_11 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_10 hCoordinate1_11]
  decide +kernel
private abbrev cSpec1_0_6 := specAt1 0 6
private theorem cFlags1_0_6 : automaticFlags (trunkCatalog.states 1).context cSpec1_0_6 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_0 coordinateInput1_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_0 hCoordinate1_3]
  decide +kernel
private abbrev cSpec1_0_7 := specAt1 0 7
private theorem cFlags1_0_7 : automaticFlags (trunkCatalog.states 1).context cSpec1_0_7 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_12 coordinateInput1_13 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_12 hCoordinate1_13]
  decide +kernel
private abbrev cSpec1_0_8 := specAt1 0 8
private theorem cFlags1_0_8 : automaticFlags (trunkCatalog.states 1).context cSpec1_0_8 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_14 coordinateInput1_15 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_14 hCoordinate1_15]
  decide +kernel
private abbrev cSpec1_0_9 := specAt1 0 9
private theorem cFlags1_0_9 : automaticFlags (trunkCatalog.states 1).context cSpec1_0_9 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_16 coordinateInput1_17 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_16 hCoordinate1_17]
  decide +kernel
private abbrev cSpec1_0_10 := specAt1 0 10
private theorem cFlags1_0_10 : automaticFlags (trunkCatalog.states 1).context cSpec1_0_10 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_18 coordinateInput1_19 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_18 hCoordinate1_19]
  decide +kernel
private abbrev cSpec1_0_11 := specAt1 0 11
private theorem cFlags1_0_11 : automaticFlags (trunkCatalog.states 1).context cSpec1_0_11 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_20 coordinateInput1_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_20 hCoordinate1_21]
  decide +kernel
private abbrev cSpec1_0_12 := specAt1 0 12
private theorem cFlags1_0_12 : automaticFlags (trunkCatalog.states 1).context cSpec1_0_12 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_22 coordinateInput1_23 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_22 hCoordinate1_23]
  decide +kernel
private abbrev cSpec1_0_13 := specAt1 0 13
private theorem cFlags1_0_13 : automaticFlags (trunkCatalog.states 1).context cSpec1_0_13 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_24 coordinateInput1_25 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_24 hCoordinate1_25]
  decide +kernel
private abbrev cSpec1_0_14 := specAt1 0 14
private theorem cFlags1_0_14 : automaticFlags (trunkCatalog.states 1).context cSpec1_0_14 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_26 coordinateInput1_27 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_26 hCoordinate1_27]
  decide +kernel
private abbrev cSpec1_0_15 := specAt1 0 15
private theorem cFlags1_0_15 : automaticFlags (trunkCatalog.states 1).context cSpec1_0_15 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_28 coordinateInput1_29 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_28 hCoordinate1_29]
  decide +kernel
private abbrev cSpec1_0_16 := specAt1 0 16
private theorem cFlags1_0_16 : automaticFlags (trunkCatalog.states 1).context cSpec1_0_16 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_2 coordinateInput1_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_2 hCoordinate1_3]
  decide +kernel
private abbrev cSpec1_0_17 := specAt1 0 17
private theorem cFlags1_0_17 : automaticFlags (trunkCatalog.states 1).context cSpec1_0_17 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_0 coordinateInput1_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_0 hCoordinate1_1]
  decide +kernel
private abbrev cSpec1_0_18 := specAt1 0 18
private theorem cFlags1_0_18 : automaticFlags (trunkCatalog.states 1).context cSpec1_0_18 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_0 coordinateInput1_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_0 hCoordinate1_21]
  decide +kernel
private abbrev cSpec1_0_19 := specAt1 0 19
private theorem cFlags1_0_19 : automaticFlags (trunkCatalog.states 1).context cSpec1_0_19 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_20 coordinateInput1_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_20 hCoordinate1_3]
  decide +kernel
private abbrev cSpec1_0_20 := specAt1 0 20
private theorem cFlags1_0_20 : automaticFlags (trunkCatalog.states 1).context cSpec1_0_20 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  rw [automaticFlags_cached _ _ coordinateInput1_2 coordinateInput1_30 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_2 hCoordinate1_30]
  decide +kernel
private abbrev cSpec1_0_21 := specAt1 0 21
private theorem cFlags1_0_21 : automaticFlags (trunkCatalog.states 1).context cSpec1_0_21 = (List.replicate 8 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_31 coordinateInput1_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_31 hCoordinate1_21]
  decide +kernel
private abbrev cSpec1_1_1 := specAt1 1 1
private theorem cFlags1_1_1 : automaticFlags (trunkCatalog.states 1).context cSpec1_1_1 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_1

private abbrev cSpec1_1_2 := specAt1 1 2
private theorem cFlags1_1_2 : automaticFlags (trunkCatalog.states 1).context cSpec1_1_2 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec1_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_2

private abbrev cSpec1_1_3 := specAt1 1 3
private theorem cFlags1_1_3 : automaticFlags (trunkCatalog.states 1).context cSpec1_1_3 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_3

private abbrev cSpec1_1_4 := specAt1 1 4
private theorem cFlags1_1_4 : automaticFlags (trunkCatalog.states 1).context cSpec1_1_4 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_4

private abbrev cSpec1_1_5 := specAt1 1 5
private theorem cFlags1_1_5 : automaticFlags (trunkCatalog.states 1).context cSpec1_1_5 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec1_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_5

private abbrev cSpec1_1_6 := specAt1 1 6
private theorem cFlags1_1_6 : automaticFlags (trunkCatalog.states 1).context cSpec1_1_6 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_6

private abbrev cSpec1_1_7 := specAt1 1 7
private theorem cFlags1_1_7 : automaticFlags (trunkCatalog.states 1).context cSpec1_1_7 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec1_0_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_7

private abbrev cSpec1_1_8 := specAt1 1 8
private theorem cFlags1_1_8 : automaticFlags (trunkCatalog.states 1).context cSpec1_1_8 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_8

private abbrev cSpec1_1_9 := specAt1 1 9
private theorem cFlags1_1_9 : automaticFlags (trunkCatalog.states 1).context cSpec1_1_9 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_9

private abbrev cSpec1_1_10 := specAt1 1 10
private theorem cFlags1_1_10 : automaticFlags (trunkCatalog.states 1).context cSpec1_1_10 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec1_0_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_10

private abbrev cSpec1_1_11 := specAt1 1 11
private theorem cFlags1_1_11 : automaticFlags (trunkCatalog.states 1).context cSpec1_1_11 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_32 coordinateInput1_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_32 hCoordinate1_33]
  decide +kernel
private abbrev cSpec1_1_12 := specAt1 1 12
private theorem cFlags1_1_12 : automaticFlags (trunkCatalog.states 1).context cSpec1_1_12 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_34 coordinateInput1_35 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_34 hCoordinate1_35]
  decide +kernel
private abbrev cSpec1_1_13 := specAt1 1 13
private theorem cFlags1_1_13 : automaticFlags (trunkCatalog.states 1).context cSpec1_1_13 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_36 coordinateInput1_37 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_36 hCoordinate1_37]
  decide +kernel
private abbrev cSpec1_1_14 := specAt1 1 14
private theorem cFlags1_1_14 : automaticFlags (trunkCatalog.states 1).context cSpec1_1_14 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_38 coordinateInput1_39 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_38 hCoordinate1_39]
  decide +kernel
private abbrev cSpec1_1_15 := specAt1 1 15
private theorem cFlags1_1_15 : automaticFlags (trunkCatalog.states 1).context cSpec1_1_15 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_40 coordinateInput1_41 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_40 hCoordinate1_41]
  decide +kernel
private abbrev cSpec1_1_16 := specAt1 1 16
private theorem cFlags1_1_16 : automaticFlags (trunkCatalog.states 1).context cSpec1_1_16 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_16

private abbrev cSpec1_1_17 := specAt1 1 17
private theorem cFlags1_1_17 : automaticFlags (trunkCatalog.states 1).context cSpec1_1_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_0_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_17

private abbrev cSpec1_1_18 := specAt1 1 18
private theorem cFlags1_1_18 : automaticFlags (trunkCatalog.states 1).context cSpec1_1_18 = (List.replicate 5 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_0 coordinateInput1_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_0 hCoordinate1_33]
  decide +kernel
private abbrev cSpec1_1_19 := specAt1 1 19
private theorem cFlags1_1_19 : automaticFlags (trunkCatalog.states 1).context cSpec1_1_19 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_32 coordinateInput1_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_32 hCoordinate1_3]
  decide +kernel
private abbrev cSpec1_1_20 := specAt1 1 20
private theorem cFlags1_1_20 : automaticFlags (trunkCatalog.states 1).context cSpec1_1_20 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  exact (automaticFlags_same _ _ cSpec1_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_20

private abbrev cSpec1_1_21 := specAt1 1 21
private theorem cFlags1_1_21 : automaticFlags (trunkCatalog.states 1).context cSpec1_1_21 = [false, true, false, false] := by
  rw [automaticFlags_cached _ _ coordinateInput1_31 coordinateInput1_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_31 hCoordinate1_33]
  decide +kernel
private abbrev cSpec1_2_1 := specAt1 2 1
private theorem cFlags1_2_1 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_1 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_1

private abbrev cSpec1_2_2 := specAt1 2 2
private theorem cFlags1_2_2 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_2 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec1_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_2

private abbrev cSpec1_2_3 := specAt1 2 3
private theorem cFlags1_2_3 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_3 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_3

private abbrev cSpec1_2_4 := specAt1 2 4
private theorem cFlags1_2_4 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_4 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_4

private abbrev cSpec1_2_5 := specAt1 2 5
private theorem cFlags1_2_5 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_5 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec1_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_5

private abbrev cSpec1_2_6 := specAt1 2 6
private theorem cFlags1_2_6 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_6 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_6

private abbrev cSpec1_2_7 := specAt1 2 7
private theorem cFlags1_2_7 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_7 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec1_0_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_7

private abbrev cSpec1_2_8 := specAt1 2 8
private theorem cFlags1_2_8 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_8 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_8

private abbrev cSpec1_2_9 := specAt1 2 9
private theorem cFlags1_2_9 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_9 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_9

private abbrev cSpec1_2_10 := specAt1 2 10
private theorem cFlags1_2_10 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_10 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec1_0_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_10

private abbrev cSpec1_2_11 := specAt1 2 11
private theorem cFlags1_2_11 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_11 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec1_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_11

private abbrev cSpec1_2_12 := specAt1 2 12
private theorem cFlags1_2_12 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_12 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_12

private abbrev cSpec1_2_13 := specAt1 2 13
private theorem cFlags1_2_13 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_13 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_13

private abbrev cSpec1_2_14 := specAt1 2 14
private theorem cFlags1_2_14 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_14 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec1_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_14

private abbrev cSpec1_2_15 := specAt1 2 15
private theorem cFlags1_2_15 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_15 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_15

private abbrev cSpec1_2_16 := specAt1 2 16
private theorem cFlags1_2_16 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_16 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_42 coordinateInput1_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_42 hCoordinate1_43]
  decide +kernel
private abbrev cSpec1_2_17 := specAt1 2 17
private theorem cFlags1_2_17 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_17 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_44 coordinateInput1_45 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_44 hCoordinate1_45]
  decide +kernel
private abbrev cSpec1_2_18 := specAt1 2 18
private theorem cFlags1_2_18 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_18 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_46 coordinateInput1_47 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_46 hCoordinate1_47]
  decide +kernel
private abbrev cSpec1_2_19 := specAt1 2 19
private theorem cFlags1_2_19 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_19 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_48 coordinateInput1_49 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_48 hCoordinate1_49]
  decide +kernel
private abbrev cSpec1_2_20 := specAt1 2 20
private theorem cFlags1_2_20 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_20 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_50 coordinateInput1_51 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_50 hCoordinate1_51]
  decide +kernel
private abbrev cSpec1_2_21 := specAt1 2 21
private theorem cFlags1_2_21 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_21 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_52 coordinateInput1_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_52 hCoordinate1_53]
  decide +kernel
private abbrev cSpec1_2_22 := specAt1 2 22
private theorem cFlags1_2_22 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_22 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_54 coordinateInput1_55 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_54 hCoordinate1_55]
  decide +kernel
private abbrev cSpec1_2_23 := specAt1 2 23
private theorem cFlags1_2_23 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_23 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_56 coordinateInput1_57 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_56 hCoordinate1_57]
  decide +kernel
private abbrev cSpec1_2_24 := specAt1 2 24
private theorem cFlags1_2_24 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_24 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_58 coordinateInput1_59 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_58 hCoordinate1_59]
  decide +kernel
private abbrev cSpec1_2_25 := specAt1 2 25
private theorem cFlags1_2_25 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_25 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_60 coordinateInput1_61 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_60 hCoordinate1_61]
  decide +kernel
private abbrev cSpec1_2_26 := specAt1 2 26
private theorem cFlags1_2_26 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_26 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_16

private abbrev cSpec1_2_27 := specAt1 2 27
private theorem cFlags1_2_27 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_0_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_17

private abbrev cSpec1_2_28 := specAt1 2 28
private theorem cFlags1_2_28 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_28 = (List.replicate 5 true) := by
  exact (automaticFlags_same _ _ cSpec1_1_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_18

private abbrev cSpec1_2_29 := specAt1 2 29
private theorem cFlags1_2_29 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_29 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec1_1_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_19

private abbrev cSpec1_2_30 := specAt1 2 30
private theorem cFlags1_2_30 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_30 = [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false] := by
  rw [automaticFlags_cached _ _ coordinateInput1_32 coordinateInput1_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_32 hCoordinate1_43]
  decide +kernel
private abbrev cSpec1_2_31 := specAt1 2 31
private theorem cFlags1_2_31 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_31 = (List.replicate 1 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_42 coordinateInput1_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_42 hCoordinate1_33]
  decide +kernel
private abbrev cSpec1_2_32 := specAt1 2 32
private theorem cFlags1_2_32 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_32 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  exact (automaticFlags_same _ _ cSpec1_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_20

private abbrev cSpec1_2_33 := specAt1 2 33
private theorem cFlags1_2_33 : automaticFlags (trunkCatalog.states 1).context cSpec1_2_33 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_31 coordinateInput1_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_31 hCoordinate1_53]
  decide +kernel
private abbrev cSpec1_3_1 := specAt1 3 1
private theorem cFlags1_3_1 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_1 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_1

private abbrev cSpec1_3_2 := specAt1 3 2
private theorem cFlags1_3_2 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_2 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec1_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_2

private abbrev cSpec1_3_3 := specAt1 3 3
private theorem cFlags1_3_3 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_3 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_3

private abbrev cSpec1_3_4 := specAt1 3 4
private theorem cFlags1_3_4 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_4 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_4

private abbrev cSpec1_3_5 := specAt1 3 5
private theorem cFlags1_3_5 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_5 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec1_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_5

private abbrev cSpec1_3_6 := specAt1 3 6
private theorem cFlags1_3_6 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_6 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_62 coordinateInput1_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_62 hCoordinate1_63]
  decide +kernel
private abbrev cSpec1_3_7 := specAt1 3 7
private theorem cFlags1_3_7 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_7 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_64 coordinateInput1_65 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_64 hCoordinate1_65]
  decide +kernel
private abbrev cSpec1_3_8 := specAt1 3 8
private theorem cFlags1_3_8 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_8 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_66 coordinateInput1_67 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_66 hCoordinate1_67]
  decide +kernel
private abbrev cSpec1_3_9 := specAt1 3 9
private theorem cFlags1_3_9 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_9 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_68 coordinateInput1_69 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_68 hCoordinate1_69]
  decide +kernel
private abbrev cSpec1_3_10 := specAt1 3 10
private theorem cFlags1_3_10 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_10 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_70 coordinateInput1_71 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_70 hCoordinate1_71]
  decide +kernel
private abbrev cSpec1_3_11 := specAt1 3 11
private theorem cFlags1_3_11 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_11 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_72 coordinateInput1_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_72 hCoordinate1_73]
  decide +kernel
private abbrev cSpec1_3_12 := specAt1 3 12
private theorem cFlags1_3_12 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_12 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_74 coordinateInput1_75 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_74 hCoordinate1_75]
  decide +kernel
private abbrev cSpec1_3_13 := specAt1 3 13
private theorem cFlags1_3_13 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_13 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_76 coordinateInput1_77 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_76 hCoordinate1_77]
  decide +kernel
private abbrev cSpec1_3_14 := specAt1 3 14
private theorem cFlags1_3_14 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_14 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_78 coordinateInput1_79 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_78 hCoordinate1_79]
  decide +kernel
private abbrev cSpec1_3_15 := specAt1 3 15
private theorem cFlags1_3_15 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_15 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_80 coordinateInput1_81 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_80 hCoordinate1_81]
  decide +kernel
private abbrev cSpec1_3_16 := specAt1 3 16
private theorem cFlags1_3_16 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_16 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_82 coordinateInput1_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_82 hCoordinate1_83]
  decide +kernel
private abbrev cSpec1_3_17 := specAt1 3 17
private theorem cFlags1_3_17 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_17 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_84 coordinateInput1_85 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_84 hCoordinate1_85]
  decide +kernel
private abbrev cSpec1_3_18 := specAt1 3 18
private theorem cFlags1_3_18 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_18 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_86 coordinateInput1_87 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_86 hCoordinate1_87]
  decide +kernel
private abbrev cSpec1_3_19 := specAt1 3 19
private theorem cFlags1_3_19 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_19 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_88 coordinateInput1_89 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_88 hCoordinate1_89]
  decide +kernel
private abbrev cSpec1_3_20 := specAt1 3 20
private theorem cFlags1_3_20 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_20 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_90 coordinateInput1_91 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_90 hCoordinate1_91]
  decide +kernel
private abbrev cSpec1_3_21 := specAt1 3 21
private theorem cFlags1_3_21 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_21 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_92 coordinateInput1_93 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_92 hCoordinate1_93]
  decide +kernel
private abbrev cSpec1_3_22 := specAt1 3 22
private theorem cFlags1_3_22 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_22 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_94 coordinateInput1_95 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_94 hCoordinate1_95]
  decide +kernel
private abbrev cSpec1_3_23 := specAt1 3 23
private theorem cFlags1_3_23 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_23 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_96 coordinateInput1_97 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_96 hCoordinate1_97]
  decide +kernel
private abbrev cSpec1_3_24 := specAt1 3 24
private theorem cFlags1_3_24 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_24 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_98 coordinateInput1_99 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_98 hCoordinate1_99]
  decide +kernel
private abbrev cSpec1_3_25 := specAt1 3 25
private theorem cFlags1_3_25 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_25 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_100 coordinateInput1_101 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_100 hCoordinate1_101]
  decide +kernel
private abbrev cSpec1_3_26 := specAt1 3 26
private theorem cFlags1_3_26 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec1_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_11

private abbrev cSpec1_3_27 := specAt1 3 27
private theorem cFlags1_3_27 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_12

private abbrev cSpec1_3_28 := specAt1 3 28
private theorem cFlags1_3_28 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_13

private abbrev cSpec1_3_29 := specAt1 3 29
private theorem cFlags1_3_29 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec1_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_14

private abbrev cSpec1_3_30 := specAt1 3 30
private theorem cFlags1_3_30 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_15

private abbrev cSpec1_3_31 := specAt1 3 31
private theorem cFlags1_3_31 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_31 = (List.replicate 20 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_2 coordinateInput1_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_2 hCoordinate1_63]
  decide +kernel
private abbrev cSpec1_3_32 := specAt1 3 32
private theorem cFlags1_3_32 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_32 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_62 coordinateInput1_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_62 hCoordinate1_1]
  decide +kernel
private abbrev cSpec1_3_33 := specAt1 3 33
private theorem cFlags1_3_33 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_33 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_62 coordinateInput1_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_62 hCoordinate1_73]
  decide +kernel
private abbrev cSpec1_3_34 := specAt1 3 34
private theorem cFlags1_3_34 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_34 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_72 coordinateInput1_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_72 hCoordinate1_63]
  decide +kernel
private abbrev cSpec1_3_35 := specAt1 3 35
private theorem cFlags1_3_35 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_35 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_72 coordinateInput1_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_72 hCoordinate1_83]
  decide +kernel
private abbrev cSpec1_3_36 := specAt1 3 36
private theorem cFlags1_3_36 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_36 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_82 coordinateInput1_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_82 hCoordinate1_73]
  decide +kernel
private abbrev cSpec1_3_37 := specAt1 3 37
private theorem cFlags1_3_37 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_37 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_82 coordinateInput1_93 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_82 hCoordinate1_93]
  decide +kernel
private abbrev cSpec1_3_38 := specAt1 3 38
private theorem cFlags1_3_38 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_38 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_92 coordinateInput1_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_92 hCoordinate1_83]
  decide +kernel
private abbrev cSpec1_3_39 := specAt1 3 39
private theorem cFlags1_3_39 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_39 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_92 coordinateInput1_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_92 hCoordinate1_33]
  decide +kernel
private abbrev cSpec1_3_40 := specAt1 3 40
private theorem cFlags1_3_40 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_40 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_32 coordinateInput1_93 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_32 hCoordinate1_93]
  decide +kernel
private abbrev cSpec1_3_41 := specAt1 3 41
private theorem cFlags1_3_41 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_41 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  exact (automaticFlags_same _ _ cSpec1_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_20

private abbrev cSpec1_3_42 := specAt1 3 42
private theorem cFlags1_3_42 : automaticFlags (trunkCatalog.states 1).context cSpec1_3_42 = [false, true, false, false] := by
  exact (automaticFlags_same _ _ cSpec1_1_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_21

private abbrev cSpec1_4_1 := specAt1 4 1
private theorem cFlags1_4_1 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_1 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_1

private abbrev cSpec1_4_2 := specAt1 4 2
private theorem cFlags1_4_2 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_2 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec1_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_2

private abbrev cSpec1_4_3 := specAt1 4 3
private theorem cFlags1_4_3 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_3 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_3

private abbrev cSpec1_4_4 := specAt1 4 4
private theorem cFlags1_4_4 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_4 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_4

private abbrev cSpec1_4_5 := specAt1 4 5
private theorem cFlags1_4_5 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_5 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec1_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_5

private abbrev cSpec1_4_6 := specAt1 4 6
private theorem cFlags1_4_6 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_6 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_6

private abbrev cSpec1_4_7 := specAt1 4 7
private theorem cFlags1_4_7 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_7 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_7

private abbrev cSpec1_4_8 := specAt1 4 8
private theorem cFlags1_4_8 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_8 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_8

private abbrev cSpec1_4_9 := specAt1 4 9
private theorem cFlags1_4_9 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_9 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_9

private abbrev cSpec1_4_10 := specAt1 4 10
private theorem cFlags1_4_10 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_10 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_10

private abbrev cSpec1_4_11 := specAt1 4 11
private theorem cFlags1_4_11 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_11 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_11

private abbrev cSpec1_4_12 := specAt1 4 12
private theorem cFlags1_4_12 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_12 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_12

private abbrev cSpec1_4_13 := specAt1 4 13
private theorem cFlags1_4_13 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_13 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_13

private abbrev cSpec1_4_14 := specAt1 4 14
private theorem cFlags1_4_14 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_14 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_14

private abbrev cSpec1_4_15 := specAt1 4 15
private theorem cFlags1_4_15 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_15 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_15

private abbrev cSpec1_4_16 := specAt1 4 16
private theorem cFlags1_4_16 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_16 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_16

private abbrev cSpec1_4_17 := specAt1 4 17
private theorem cFlags1_4_17 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_17

private abbrev cSpec1_4_18 := specAt1 4 18
private theorem cFlags1_4_18 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_18 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_18

private abbrev cSpec1_4_19 := specAt1 4 19
private theorem cFlags1_4_19 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_19 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_19

private abbrev cSpec1_4_20 := specAt1 4 20
private theorem cFlags1_4_20 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_20 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_20

private abbrev cSpec1_4_21 := specAt1 4 21
private theorem cFlags1_4_21 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_21 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_21

private abbrev cSpec1_4_22 := specAt1 4 22
private theorem cFlags1_4_22 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_22 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_22

private abbrev cSpec1_4_23 := specAt1 4 23
private theorem cFlags1_4_23 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_23 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_23

private abbrev cSpec1_4_24 := specAt1 4 24
private theorem cFlags1_4_24 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_24 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_24

private abbrev cSpec1_4_25 := specAt1 4 25
private theorem cFlags1_4_25 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_25 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_25

private abbrev cSpec1_4_26 := specAt1 4 26
private theorem cFlags1_4_26 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec1_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_11

private abbrev cSpec1_4_27 := specAt1 4 27
private theorem cFlags1_4_27 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_12

private abbrev cSpec1_4_28 := specAt1 4 28
private theorem cFlags1_4_28 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_13

private abbrev cSpec1_4_29 := specAt1 4 29
private theorem cFlags1_4_29 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec1_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_14

private abbrev cSpec1_4_30 := specAt1 4 30
private theorem cFlags1_4_30 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_15

private abbrev cSpec1_4_31 := specAt1 4 31
private theorem cFlags1_4_31 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_31 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec1_2_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_16

private abbrev cSpec1_4_32 := specAt1 4 32
private theorem cFlags1_4_32 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_32 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_2_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_17

private abbrev cSpec1_4_33 := specAt1 4 33
private theorem cFlags1_4_33 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_33 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec1_2_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_18

private abbrev cSpec1_4_34 := specAt1 4 34
private theorem cFlags1_4_34 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_34 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_2_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_19

private abbrev cSpec1_4_35 := specAt1 4 35
private theorem cFlags1_4_35 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_35 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec1_2_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_20

private abbrev cSpec1_4_36 := specAt1 4 36
private theorem cFlags1_4_36 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_36 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec1_2_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_21

private abbrev cSpec1_4_37 := specAt1 4 37
private theorem cFlags1_4_37 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_37 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec1_2_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_22

private abbrev cSpec1_4_38 := specAt1 4 38
private theorem cFlags1_4_38 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_38 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_2_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_23

private abbrev cSpec1_4_39 := specAt1 4 39
private theorem cFlags1_4_39 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_39 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec1_2_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_24

private abbrev cSpec1_4_40 := specAt1 4 40
private theorem cFlags1_4_40 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_40 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_2_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_25

private abbrev cSpec1_4_41 := specAt1 4 41
private theorem cFlags1_4_41 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_41 = (List.replicate 20 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_31

private abbrev cSpec1_4_42 := specAt1 4 42
private theorem cFlags1_4_42 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_42 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_32

private abbrev cSpec1_4_43 := specAt1 4 43
private theorem cFlags1_4_43 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_43 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_33 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_33

private abbrev cSpec1_4_44 := specAt1 4 44
private theorem cFlags1_4_44 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_44 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_34 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_34

private abbrev cSpec1_4_45 := specAt1 4 45
private theorem cFlags1_4_45 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_45 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_35 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_35

private abbrev cSpec1_4_46 := specAt1 4 46
private theorem cFlags1_4_46 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_46 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_36 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_36

private abbrev cSpec1_4_47 := specAt1 4 47
private theorem cFlags1_4_47 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_47 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_37 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_37

private abbrev cSpec1_4_48 := specAt1 4 48
private theorem cFlags1_4_48 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_48 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_38 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_38

private abbrev cSpec1_4_49 := specAt1 4 49
private theorem cFlags1_4_49 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_49 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_39 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_39

private abbrev cSpec1_4_50 := specAt1 4 50
private theorem cFlags1_4_50 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_50 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_40 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_40

private abbrev cSpec1_4_51 := specAt1 4 51
private theorem cFlags1_4_51 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_51 = [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false] := by
  exact (automaticFlags_same _ _ cSpec1_2_30 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_30

private abbrev cSpec1_4_52 := specAt1 4 52
private theorem cFlags1_4_52 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_52 = (List.replicate 1 false) := by
  exact (automaticFlags_same _ _ cSpec1_2_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_31

private abbrev cSpec1_4_53 := specAt1 4 53
private theorem cFlags1_4_53 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_53 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  exact (automaticFlags_same _ _ cSpec1_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_20

private abbrev cSpec1_4_54 := specAt1 4 54
private theorem cFlags1_4_54 : automaticFlags (trunkCatalog.states 1).context cSpec1_4_54 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec1_2_33 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_33

private abbrev cSpec1_5_1 := specAt1 5 1
private theorem cFlags1_5_1 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_1 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_1

private abbrev cSpec1_5_2 := specAt1 5 2
private theorem cFlags1_5_2 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_2 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec1_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_2

private abbrev cSpec1_5_3 := specAt1 5 3
private theorem cFlags1_5_3 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_3 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_3

private abbrev cSpec1_5_4 := specAt1 5 4
private theorem cFlags1_5_4 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_4 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_4

private abbrev cSpec1_5_5 := specAt1 5 5
private theorem cFlags1_5_5 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_5 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec1_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_5

private abbrev cSpec1_5_6 := specAt1 5 6
private theorem cFlags1_5_6 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_6 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_6

private abbrev cSpec1_5_7 := specAt1 5 7
private theorem cFlags1_5_7 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_7 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_7

private abbrev cSpec1_5_8 := specAt1 5 8
private theorem cFlags1_5_8 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_8 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_8

private abbrev cSpec1_5_9 := specAt1 5 9
private theorem cFlags1_5_9 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_9 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_9

private abbrev cSpec1_5_10 := specAt1 5 10
private theorem cFlags1_5_10 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_10 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_10

private abbrev cSpec1_5_11 := specAt1 5 11
private theorem cFlags1_5_11 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_11 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_102 coordinateInput1_103 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_102 hCoordinate1_103]
  decide +kernel
private abbrev cSpec1_5_12 := specAt1 5 12
private theorem cFlags1_5_12 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_12 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_104 coordinateInput1_105 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_104 hCoordinate1_105]
  decide +kernel
private abbrev cSpec1_5_13 := specAt1 5 13
private theorem cFlags1_5_13 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_13 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_106 coordinateInput1_107 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_106 hCoordinate1_107]
  decide +kernel
private abbrev cSpec1_5_14 := specAt1 5 14
private theorem cFlags1_5_14 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_14 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_108 coordinateInput1_109 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_108 hCoordinate1_109]
  decide +kernel
private abbrev cSpec1_5_15 := specAt1 5 15
private theorem cFlags1_5_15 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_15 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_110 coordinateInput1_111 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_110 hCoordinate1_111]
  decide +kernel
private abbrev cSpec1_5_16 := specAt1 5 16
private theorem cFlags1_5_16 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_16 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_16

private abbrev cSpec1_5_17 := specAt1 5 17
private theorem cFlags1_5_17 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_17

private abbrev cSpec1_5_18 := specAt1 5 18
private theorem cFlags1_5_18 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_18 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_18

private abbrev cSpec1_5_19 := specAt1 5 19
private theorem cFlags1_5_19 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_19 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_19

private abbrev cSpec1_5_20 := specAt1 5 20
private theorem cFlags1_5_20 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_20 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_20

private abbrev cSpec1_5_21 := specAt1 5 21
private theorem cFlags1_5_21 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_21 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_21

private abbrev cSpec1_5_22 := specAt1 5 22
private theorem cFlags1_5_22 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_22 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_22

private abbrev cSpec1_5_23 := specAt1 5 23
private theorem cFlags1_5_23 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_23 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_23

private abbrev cSpec1_5_24 := specAt1 5 24
private theorem cFlags1_5_24 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_24 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_24

private abbrev cSpec1_5_25 := specAt1 5 25
private theorem cFlags1_5_25 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_25 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_25

private abbrev cSpec1_5_26 := specAt1 5 26
private theorem cFlags1_5_26 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec1_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_11

private abbrev cSpec1_5_27 := specAt1 5 27
private theorem cFlags1_5_27 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_12

private abbrev cSpec1_5_28 := specAt1 5 28
private theorem cFlags1_5_28 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_13

private abbrev cSpec1_5_29 := specAt1 5 29
private theorem cFlags1_5_29 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec1_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_14

private abbrev cSpec1_5_30 := specAt1 5 30
private theorem cFlags1_5_30 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_15

private abbrev cSpec1_5_31 := specAt1 5 31
private theorem cFlags1_5_31 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_31 = (List.replicate 20 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_31

private abbrev cSpec1_5_32 := specAt1 5 32
private theorem cFlags1_5_32 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_32 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_32

private abbrev cSpec1_5_33 := specAt1 5 33
private theorem cFlags1_5_33 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_33 = (List.replicate 8 true) := by
  rw [automaticFlags_cached _ _ coordinateInput1_62 coordinateInput1_103 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_62 hCoordinate1_103]
  decide +kernel
private abbrev cSpec1_5_34 := specAt1 5 34
private theorem cFlags1_5_34 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_34 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_102 coordinateInput1_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_102 hCoordinate1_63]
  decide +kernel
private abbrev cSpec1_5_35 := specAt1 5 35
private theorem cFlags1_5_35 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_35 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_102 coordinateInput1_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_102 hCoordinate1_83]
  decide +kernel
private abbrev cSpec1_5_36 := specAt1 5 36
private theorem cFlags1_5_36 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_36 = (List.replicate 8 false) := by
  rw [automaticFlags_cached _ _ coordinateInput1_82 coordinateInput1_103 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate1_82 hCoordinate1_103]
  decide +kernel
private abbrev cSpec1_5_37 := specAt1 5 37
private theorem cFlags1_5_37 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_37 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_37 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_37

private abbrev cSpec1_5_38 := specAt1 5 38
private theorem cFlags1_5_38 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_38 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_38 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_38

private abbrev cSpec1_5_39 := specAt1 5 39
private theorem cFlags1_5_39 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_39 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_39 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_39

private abbrev cSpec1_5_40 := specAt1 5 40
private theorem cFlags1_5_40 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_40 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_40 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_40

private abbrev cSpec1_5_41 := specAt1 5 41
private theorem cFlags1_5_41 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_41 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  exact (automaticFlags_same _ _ cSpec1_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_20

private abbrev cSpec1_5_42 := specAt1 5 42
private theorem cFlags1_5_42 : automaticFlags (trunkCatalog.states 1).context cSpec1_5_42 = [false, true, false, false] := by
  exact (automaticFlags_same _ _ cSpec1_1_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_21

private abbrev cSpec1_6_1 := specAt1 6 1
private theorem cFlags1_6_1 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_1 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_1

private abbrev cSpec1_6_2 := specAt1 6 2
private theorem cFlags1_6_2 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_2 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec1_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_2

private abbrev cSpec1_6_3 := specAt1 6 3
private theorem cFlags1_6_3 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_3 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_3

private abbrev cSpec1_6_4 := specAt1 6 4
private theorem cFlags1_6_4 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_4 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec1_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_4

private abbrev cSpec1_6_5 := specAt1 6 5
private theorem cFlags1_6_5 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_5 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec1_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_5

private abbrev cSpec1_6_6 := specAt1 6 6
private theorem cFlags1_6_6 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_6 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_6

private abbrev cSpec1_6_7 := specAt1 6 7
private theorem cFlags1_6_7 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_7 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_7

private abbrev cSpec1_6_8 := specAt1 6 8
private theorem cFlags1_6_8 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_8 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_8

private abbrev cSpec1_6_9 := specAt1 6 9
private theorem cFlags1_6_9 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_9 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_9

private abbrev cSpec1_6_10 := specAt1 6 10
private theorem cFlags1_6_10 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_10 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_10

private abbrev cSpec1_6_11 := specAt1 6 11
private theorem cFlags1_6_11 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_11 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_5_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_5_11

private abbrev cSpec1_6_12 := specAt1 6 12
private theorem cFlags1_6_12 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_12 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec1_5_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_5_12

private abbrev cSpec1_6_13 := specAt1 6 13
private theorem cFlags1_6_13 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_13 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec1_5_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_5_13

private abbrev cSpec1_6_14 := specAt1 6 14
private theorem cFlags1_6_14 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_14 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec1_5_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_5_14

private abbrev cSpec1_6_15 := specAt1 6 15
private theorem cFlags1_6_15 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_15 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec1_5_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_5_15

private abbrev cSpec1_6_16 := specAt1 6 16
private theorem cFlags1_6_16 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_16 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_16

private abbrev cSpec1_6_17 := specAt1 6 17
private theorem cFlags1_6_17 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_17

private abbrev cSpec1_6_18 := specAt1 6 18
private theorem cFlags1_6_18 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_18 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_18

private abbrev cSpec1_6_19 := specAt1 6 19
private theorem cFlags1_6_19 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_19 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_19

private abbrev cSpec1_6_20 := specAt1 6 20
private theorem cFlags1_6_20 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_20 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_20

private abbrev cSpec1_6_21 := specAt1 6 21
private theorem cFlags1_6_21 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_21 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_21

private abbrev cSpec1_6_22 := specAt1 6 22
private theorem cFlags1_6_22 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_22 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_22

private abbrev cSpec1_6_23 := specAt1 6 23
private theorem cFlags1_6_23 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_23 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_23

private abbrev cSpec1_6_24 := specAt1 6 24
private theorem cFlags1_6_24 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_24 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_24

private abbrev cSpec1_6_25 := specAt1 6 25
private theorem cFlags1_6_25 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_25 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_25

private abbrev cSpec1_6_26 := specAt1 6 26
private theorem cFlags1_6_26 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec1_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_11

private abbrev cSpec1_6_27 := specAt1 6 27
private theorem cFlags1_6_27 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec1_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_12

private abbrev cSpec1_6_28 := specAt1 6 28
private theorem cFlags1_6_28 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_13

private abbrev cSpec1_6_29 := specAt1 6 29
private theorem cFlags1_6_29 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec1_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_14

private abbrev cSpec1_6_30 := specAt1 6 30
private theorem cFlags1_6_30 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_1_15

private abbrev cSpec1_6_31 := specAt1 6 31
private theorem cFlags1_6_31 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_31 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec1_2_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_16

private abbrev cSpec1_6_32 := specAt1 6 32
private theorem cFlags1_6_32 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_32 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_2_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_17

private abbrev cSpec1_6_33 := specAt1 6 33
private theorem cFlags1_6_33 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_33 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec1_2_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_18

private abbrev cSpec1_6_34 := specAt1 6 34
private theorem cFlags1_6_34 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_34 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_2_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_19

private abbrev cSpec1_6_35 := specAt1 6 35
private theorem cFlags1_6_35 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_35 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec1_2_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_20

private abbrev cSpec1_6_36 := specAt1 6 36
private theorem cFlags1_6_36 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_36 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec1_2_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_21

private abbrev cSpec1_6_37 := specAt1 6 37
private theorem cFlags1_6_37 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_37 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec1_2_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_22

private abbrev cSpec1_6_38 := specAt1 6 38
private theorem cFlags1_6_38 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_38 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_2_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_23

private abbrev cSpec1_6_39 := specAt1 6 39
private theorem cFlags1_6_39 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_39 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec1_2_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_24

private abbrev cSpec1_6_40 := specAt1 6 40
private theorem cFlags1_6_40 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_40 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec1_2_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_25

private abbrev cSpec1_6_41 := specAt1 6 41
private theorem cFlags1_6_41 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_41 = (List.replicate 20 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_31

private abbrev cSpec1_6_42 := specAt1 6 42
private theorem cFlags1_6_42 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_42 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_32

private abbrev cSpec1_6_43 := specAt1 6 43
private theorem cFlags1_6_43 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_43 = (List.replicate 8 true) := by
  exact (automaticFlags_same _ _ cSpec1_5_33 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_5_33

private abbrev cSpec1_6_44 := specAt1 6 44
private theorem cFlags1_6_44 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_44 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec1_5_34 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_5_34

private abbrev cSpec1_6_45 := specAt1 6 45
private theorem cFlags1_6_45 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_45 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec1_5_35 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_5_35

private abbrev cSpec1_6_46 := specAt1 6 46
private theorem cFlags1_6_46 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_46 = (List.replicate 8 false) := by
  exact (automaticFlags_same _ _ cSpec1_5_36 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_5_36

private abbrev cSpec1_6_47 := specAt1 6 47
private theorem cFlags1_6_47 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_47 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec1_3_37 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_37

private abbrev cSpec1_6_48 := specAt1 6 48
private theorem cFlags1_6_48 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_48 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_38 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_38

private abbrev cSpec1_6_49 := specAt1 6 49
private theorem cFlags1_6_49 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_49 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_39 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_39

private abbrev cSpec1_6_50 := specAt1 6 50
private theorem cFlags1_6_50 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_50 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec1_3_40 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_3_40

private abbrev cSpec1_6_51 := specAt1 6 51
private theorem cFlags1_6_51 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_51 = [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false] := by
  exact (automaticFlags_same _ _ cSpec1_2_30 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_30

private abbrev cSpec1_6_52 := specAt1 6 52
private theorem cFlags1_6_52 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_52 = (List.replicate 1 false) := by
  exact (automaticFlags_same _ _ cSpec1_2_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_31

private abbrev cSpec1_6_53 := specAt1 6 53
private theorem cFlags1_6_53 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_53 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  exact (automaticFlags_same _ _ cSpec1_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_0_20

private abbrev cSpec1_6_54 := specAt1 6 54
private theorem cFlags1_6_54 : automaticFlags (trunkCatalog.states 1).context cSpec1_6_54 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec1_2_33 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags1_2_33

private theorem keys_eq : coverageKeys (trunkCatalog.states 1) = checkedKeys := by
  rfl
private theorem tasks_eq : coverageTasks (trunkCatalog.states 1) = checkedTasks := by
  rw [← coverageTasksProjection_eq]
  change [(0,[(1, (automaticFlags (trunkCatalog.states 1).context cSpec1_0_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 1).context cSpec1_0_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 1).context cSpec1_0_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 1).context cSpec1_0_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 1).context cSpec1_0_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 1).context cSpec1_0_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 1).context cSpec1_0_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 1).context cSpec1_0_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 1).context cSpec1_0_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 1).context cSpec1_0_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 1).context cSpec1_0_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 1).context cSpec1_0_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 1).context cSpec1_0_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 1).context cSpec1_0_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 1).context cSpec1_0_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 1).context cSpec1_0_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 1).context cSpec1_0_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 1).context cSpec1_0_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 1).context cSpec1_0_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 1).context cSpec1_0_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 1).context cSpec1_0_21).zipIdx.map Prod.swap)]),(1,[(1, (automaticFlags (trunkCatalog.states 1).context cSpec1_1_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 1).context cSpec1_1_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 1).context cSpec1_1_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 1).context cSpec1_1_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 1).context cSpec1_1_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 1).context cSpec1_1_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 1).context cSpec1_1_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 1).context cSpec1_1_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 1).context cSpec1_1_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 1).context cSpec1_1_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 1).context cSpec1_1_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 1).context cSpec1_1_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 1).context cSpec1_1_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 1).context cSpec1_1_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 1).context cSpec1_1_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 1).context cSpec1_1_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 1).context cSpec1_1_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 1).context cSpec1_1_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 1).context cSpec1_1_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 1).context cSpec1_1_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 1).context cSpec1_1_21).zipIdx.map Prod.swap)]),(2,[(1, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 1).context cSpec1_2_33).zipIdx.map Prod.swap)]),(3,[(1, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 1).context cSpec1_3_42).zipIdx.map Prod.swap)]),(4,[(1, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_42).zipIdx.map Prod.swap),(43, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_43).zipIdx.map Prod.swap),(44, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_44).zipIdx.map Prod.swap),(45, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_45).zipIdx.map Prod.swap),(46, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_46).zipIdx.map Prod.swap),(47, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_47).zipIdx.map Prod.swap),(48, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_48).zipIdx.map Prod.swap),(49, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_49).zipIdx.map Prod.swap),(50, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_50).zipIdx.map Prod.swap),(51, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_51).zipIdx.map Prod.swap),(52, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_52).zipIdx.map Prod.swap),(53, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_53).zipIdx.map Prod.swap),(54, (automaticFlags (trunkCatalog.states 1).context cSpec1_4_54).zipIdx.map Prod.swap)]),(5,[(1, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 1).context cSpec1_5_42).zipIdx.map Prod.swap)]),(6,[(1, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_42).zipIdx.map Prod.swap),(43, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_43).zipIdx.map Prod.swap),(44, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_44).zipIdx.map Prod.swap),(45, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_45).zipIdx.map Prod.swap),(46, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_46).zipIdx.map Prod.swap),(47, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_47).zipIdx.map Prod.swap),(48, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_48).zipIdx.map Prod.swap),(49, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_49).zipIdx.map Prod.swap),(50, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_50).zipIdx.map Prod.swap),(51, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_51).zipIdx.map Prod.swap),(52, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_52).zipIdx.map Prod.swap),(53, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_53).zipIdx.map Prod.swap),(54, (automaticFlags (trunkCatalog.states 1).context cSpec1_6_54).zipIdx.map Prod.swap)])] = checkedTasks
  simp only [cFlags1_0_1, cFlags1_0_2, cFlags1_0_3, cFlags1_0_4, cFlags1_0_5, cFlags1_0_6, cFlags1_0_7, cFlags1_0_8, cFlags1_0_9, cFlags1_0_10, cFlags1_0_11, cFlags1_0_12, cFlags1_0_13, cFlags1_0_14, cFlags1_0_15, cFlags1_0_16, cFlags1_0_17, cFlags1_0_18, cFlags1_0_19, cFlags1_0_20, cFlags1_0_21, cFlags1_1_1, cFlags1_1_2, cFlags1_1_3, cFlags1_1_4, cFlags1_1_5, cFlags1_1_6, cFlags1_1_7, cFlags1_1_8, cFlags1_1_9, cFlags1_1_10, cFlags1_1_11, cFlags1_1_12, cFlags1_1_13, cFlags1_1_14, cFlags1_1_15, cFlags1_1_16, cFlags1_1_17, cFlags1_1_18, cFlags1_1_19, cFlags1_1_20, cFlags1_1_21, cFlags1_2_1, cFlags1_2_2, cFlags1_2_3, cFlags1_2_4, cFlags1_2_5, cFlags1_2_6, cFlags1_2_7, cFlags1_2_8, cFlags1_2_9, cFlags1_2_10, cFlags1_2_11, cFlags1_2_12, cFlags1_2_13, cFlags1_2_14, cFlags1_2_15, cFlags1_2_16, cFlags1_2_17, cFlags1_2_18, cFlags1_2_19, cFlags1_2_20, cFlags1_2_21, cFlags1_2_22, cFlags1_2_23, cFlags1_2_24, cFlags1_2_25, cFlags1_2_26, cFlags1_2_27, cFlags1_2_28, cFlags1_2_29, cFlags1_2_30, cFlags1_2_31, cFlags1_2_32, cFlags1_2_33, cFlags1_3_1, cFlags1_3_2, cFlags1_3_3, cFlags1_3_4, cFlags1_3_5, cFlags1_3_6, cFlags1_3_7, cFlags1_3_8, cFlags1_3_9, cFlags1_3_10, cFlags1_3_11, cFlags1_3_12, cFlags1_3_13, cFlags1_3_14, cFlags1_3_15, cFlags1_3_16, cFlags1_3_17, cFlags1_3_18, cFlags1_3_19, cFlags1_3_20, cFlags1_3_21, cFlags1_3_22, cFlags1_3_23, cFlags1_3_24, cFlags1_3_25, cFlags1_3_26, cFlags1_3_27, cFlags1_3_28, cFlags1_3_29, cFlags1_3_30, cFlags1_3_31, cFlags1_3_32, cFlags1_3_33, cFlags1_3_34, cFlags1_3_35, cFlags1_3_36, cFlags1_3_37, cFlags1_3_38, cFlags1_3_39, cFlags1_3_40, cFlags1_3_41, cFlags1_3_42, cFlags1_4_1, cFlags1_4_2, cFlags1_4_3, cFlags1_4_4, cFlags1_4_5, cFlags1_4_6, cFlags1_4_7, cFlags1_4_8, cFlags1_4_9, cFlags1_4_10, cFlags1_4_11, cFlags1_4_12, cFlags1_4_13, cFlags1_4_14, cFlags1_4_15, cFlags1_4_16, cFlags1_4_17, cFlags1_4_18, cFlags1_4_19, cFlags1_4_20, cFlags1_4_21, cFlags1_4_22, cFlags1_4_23, cFlags1_4_24, cFlags1_4_25, cFlags1_4_26, cFlags1_4_27, cFlags1_4_28, cFlags1_4_29, cFlags1_4_30, cFlags1_4_31, cFlags1_4_32, cFlags1_4_33, cFlags1_4_34, cFlags1_4_35, cFlags1_4_36, cFlags1_4_37, cFlags1_4_38, cFlags1_4_39, cFlags1_4_40, cFlags1_4_41, cFlags1_4_42, cFlags1_4_43, cFlags1_4_44, cFlags1_4_45, cFlags1_4_46, cFlags1_4_47, cFlags1_4_48, cFlags1_4_49, cFlags1_4_50, cFlags1_4_51, cFlags1_4_52, cFlags1_4_53, cFlags1_4_54, cFlags1_5_1, cFlags1_5_2, cFlags1_5_3, cFlags1_5_4, cFlags1_5_5, cFlags1_5_6, cFlags1_5_7, cFlags1_5_8, cFlags1_5_9, cFlags1_5_10, cFlags1_5_11, cFlags1_5_12, cFlags1_5_13, cFlags1_5_14, cFlags1_5_15, cFlags1_5_16, cFlags1_5_17, cFlags1_5_18, cFlags1_5_19, cFlags1_5_20, cFlags1_5_21, cFlags1_5_22, cFlags1_5_23, cFlags1_5_24, cFlags1_5_25, cFlags1_5_26, cFlags1_5_27, cFlags1_5_28, cFlags1_5_29, cFlags1_5_30, cFlags1_5_31, cFlags1_5_32, cFlags1_5_33, cFlags1_5_34, cFlags1_5_35, cFlags1_5_36, cFlags1_5_37, cFlags1_5_38, cFlags1_5_39, cFlags1_5_40, cFlags1_5_41, cFlags1_5_42, cFlags1_6_1, cFlags1_6_2, cFlags1_6_3, cFlags1_6_4, cFlags1_6_5, cFlags1_6_6, cFlags1_6_7, cFlags1_6_8, cFlags1_6_9, cFlags1_6_10, cFlags1_6_11, cFlags1_6_12, cFlags1_6_13, cFlags1_6_14, cFlags1_6_15, cFlags1_6_16, cFlags1_6_17, cFlags1_6_18, cFlags1_6_19, cFlags1_6_20, cFlags1_6_21, cFlags1_6_22, cFlags1_6_23, cFlags1_6_24, cFlags1_6_25, cFlags1_6_26, cFlags1_6_27, cFlags1_6_28, cFlags1_6_29, cFlags1_6_30, cFlags1_6_31, cFlags1_6_32, cFlags1_6_33, cFlags1_6_34, cFlags1_6_35, cFlags1_6_36, cFlags1_6_37, cFlags1_6_38, cFlags1_6_39, cFlags1_6_40, cFlags1_6_41, cFlags1_6_42, cFlags1_6_43, cFlags1_6_44, cFlags1_6_45, cFlags1_6_46, cFlags1_6_47, cFlags1_6_48, cFlags1_6_49, cFlags1_6_50, cFlags1_6_51, cFlags1_6_52, cFlags1_6_53, cFlags1_6_54]
  rfl
private theorem parents_length : (trunkRawParents (trunkCatalog.states 1).context).length = 625 := by
  decide +kernel
private theorem table_checked : coverageTable checkedKeys checkedTasks 625 := by
  apply coveragePlanRemainder_sound checkedPlanKeys _ _ [[179, 304, 359], [], [304, 359, 484, 489, 609], [489, 499], [484, 489], [489, 499], []]
  unfold coveragePlanRemainder coverageRemainder parentsFor
  decide +kernel

theorem solution : trunkCoverage trunkCatalog 1 := by
  apply coverageTable_sound 1
  · unfold certRectangleValid; decide +kernel
  · decide +kernel
  · rw [keys_eq, tasks_eq, parents_length]
    exact table_checked
#print axioms solution
