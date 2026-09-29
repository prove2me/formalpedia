-- Prove2me | solution 1 for Freiman.trunk_coverage_08
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:49:26.386528+00:00
-- url     : https://prove2.me/submissions/36c49366-c029-4e84-a492-b5e08d379fee

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

private def coordinateFields8 : Array CertField := #[⟨(4/13),(1/13),(0/1),(0/1)⟩,⟨(1/2),(1/6),(0/1),(0/1)⟩,⟨(52/73),(1/73),(0/1),(0/1)⟩,⟨(89/214),(1/214),(0/1),(0/1)⟩,⟨(9/13),(-1/13),(0/1),(0/1)⟩,⟨(2/1),(-1/1),(0/1),(0/1)⟩,⟨(15/37),(-1/37),(0/1),(0/1)⟩,⟨(125/214),(-1/214),(0/1),(0/1)⟩,⟨(66/179),(-1/537),(0/1),(0/1)⟩,⟨(22/37),(1/37),(0/1),(0/1)⟩,⟨(113/179),(1/537),(0/1),(0/1)⟩,⟨(17/22),(-1/22),(0/1),(0/1)⟩,⟨(101/143),(-1/429),(0/1),(0/1)⟩,⟨(735/1006),(1/1006),(0/1),(0/1)⟩,⟨(35/94),(1/94),(0/1),(0/1)⟩,⟨(553/1429),(1/1429),(0/1),(0/1)⟩,⟨(10/23),(-1/69),(0/1),(0/1)⟩,⟨(517/1249),(-1/1249),(0/1),(0/1)⟩,⟨(1272/3013),(1/3013),(0/1),(0/1)⟩,⟨(5/22),(1/22),(0/1),(0/1)⟩,⟨(42/143),(1/429),(0/1),(0/1)⟩,⟨(271/1006),(-1/1006),(0/1),(0/1)⟩,⟨(16/59),(1/177),(0/1),(0/1)⟩,⟨(767/2749),(1/2749),(0/1),(0/1)⟩,⟨(43/142),(-1/142),(0/1),(0/1)⟩,⟨(731/2497),(-1/2497),(0/1),(0/1)⟩,⟨(1809/6094),(1/6094),(0/1),(0/1)⟩,⟨(3289/10753),(1/10753),(0/1),(0/1)⟩,⟨(71/229),(-1/229),(0/1),(0/1)⟩,⟨(1413/4654),(-1/4654),(0/1),(0/1)⟩,⟨(6697/22079),(-1/66237),(0/1),(0/1)⟩,⟨(469/1549),(1/1549),(0/1),(0/1)⟩,⟨(579/1894),(-1/1894),(0/1),(0/1)⟩,⟨(9014/29557),(-1/29557),(0/1),(0/1)⟩,⟨(13/23),(1/69),(0/1),(0/1)⟩,⟨(732/1249),(1/1249),(0/1),(0/1)⟩,⟨(59/94),(-1/94),(0/1),(0/1)⟩]
private abbrev coordinateInput8_0 : LowerPair × Bool × Bool := (([2], []), true, false)
private def coordinateCodes8_0 : List (ℕ × ℕ) := [(0, 1), (0, 1), (0, 2), (0, 1), (3, 1)]
private abbrev coordinateInput8_1 : LowerPair × Bool × Bool := (([1], []), false, false)
private def coordinateCodes8_1 : List (ℕ × ℕ) := [(4, 5), (4, 6), (4, 5), (7, 5), (4, 5)]
private abbrev coordinateInput8_2 : LowerPair × Bool × Bool := (([1], []), true, false)
private def coordinateCodes8_2 : List (ℕ × ℕ) := [(2, 1), (2, 1)]
private abbrev coordinateInput8_3 : LowerPair × Bool × Bool := (([2], []), false, false)
private def coordinateCodes8_3 : List (ℕ × ℕ) := [(6, 5), (6, 6), (6, 5), (8, 5), (6, 5)]
private abbrev coordinateInput8_4 : LowerPair × Bool × Bool := (([1, 1], []), true, false)
private def coordinateCodes8_4 : List (ℕ × ℕ) := [(9, 1), (9, 2), (9, 1), (10, 1)]
private abbrev coordinateInput8_5 : LowerPair × Bool × Bool := (([1, 2], []), false, false)
private def coordinateCodes8_5 : List (ℕ × ℕ) := [(11, 5), (11, 6), (11, 5), (12, 5)]
private abbrev coordinateInput8_6 : LowerPair × Bool × Bool := (([1, 2], []), true, false)
private def coordinateCodes8_6 : List (ℕ × ℕ) := [(2, 1), (2, 2), (2, 1), (13, 1)]
private abbrev coordinateInput8_7 : LowerPair × Bool × Bool := (([1, 1], []), false, false)
private def coordinateCodes8_7 : List (ℕ × ℕ) := [(4, 5), (4, 6), (4, 5), (7, 5)]
private abbrev coordinateInput8_8 : LowerPair × Bool × Bool := (([1], [1]), true, true)
private def coordinateCodes8_8 : List (ℕ × ℕ) := [(2, 1)]
private abbrev coordinateInput8_9 : LowerPair × Bool × Bool := (([1], [2]), false, true)
private def coordinateCodes8_9 : List (ℕ × ℕ) := [(4, 6), (4, 8), (4, 6), (7, 6)]
private abbrev coordinateInput8_10 : LowerPair × Bool × Bool := (([1], [2]), true, true)
private def coordinateCodes8_10 : List (ℕ × ℕ) := [(2, 0)]
private abbrev coordinateInput8_11 : LowerPair × Bool × Bool := (([1], [1]), false, true)
private def coordinateCodes8_11 : List (ℕ × ℕ) := [(4, 4), (4, 7), (4, 4), (7, 4)]
private abbrev coordinateInput8_12 : LowerPair × Bool × Bool := (([2, 1], []), true, false)
private def coordinateCodes8_12 : List (ℕ × ℕ) := [(14, 1), (14, 2), (14, 1), (15, 1)]
private abbrev coordinateInput8_13 : LowerPair × Bool × Bool := (([2, 2], []), false, false)
private def coordinateCodes8_13 : List (ℕ × ℕ) := [(16, 5), (16, 6), (16, 5), (17, 5)]
private abbrev coordinateInput8_14 : LowerPair × Bool × Bool := (([2, 2], []), true, false)
private def coordinateCodes8_14 : List (ℕ × ℕ) := [(3, 1), (3, 2), (3, 1), (18, 1)]
private abbrev coordinateInput8_15 : LowerPair × Bool × Bool := (([2, 1], []), false, false)
private def coordinateCodes8_15 : List (ℕ × ℕ) := [(6, 5), (6, 6), (6, 5), (8, 5)]
private abbrev coordinateInput8_16 : LowerPair × Bool × Bool := (([2], [1]), true, true)
private def coordinateCodes8_16 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 1), (3, 1)]
private abbrev coordinateInput8_17 : LowerPair × Bool × Bool := (([2], [2]), false, true)
private def coordinateCodes8_17 : List (ℕ × ℕ) := [(6, 6), (6, 8), (6, 6), (8, 6)]
private abbrev coordinateInput8_18 : LowerPair × Bool × Bool := (([2], [2]), true, true)
private def coordinateCodes8_18 : List (ℕ × ℕ) := [(0, 0), (0, 3), (0, 0), (3, 0)]
private abbrev coordinateInput8_19 : LowerPair × Bool × Bool := (([2], [1]), false, true)
private def coordinateCodes8_19 : List (ℕ × ℕ) := [(6, 4), (6, 7), (6, 4), (8, 4)]
private abbrev coordinateInput8_20 : LowerPair × Bool × Bool := (([3], []), true, false)
private def coordinateCodes8_20 : List (ℕ × ℕ) := [(19, 1), (19, 1), (19, 2), (19, 1), (20, 1)]
private abbrev coordinateInput8_21 : LowerPair × Bool × Bool := (([3], []), false, false)
private def coordinateCodes8_21 : List (ℕ × ℕ) := [(21, 5), (21, 5)]
private abbrev coordinateInput8_22 : LowerPair × Bool × Bool := (([3, 1], []), true, false)
private def coordinateCodes8_22 : List (ℕ × ℕ) := [(22, 1), (22, 2), (22, 1), (23, 1)]
private abbrev coordinateInput8_23 : LowerPair × Bool × Bool := (([3, 2], []), false, false)
private def coordinateCodes8_23 : List (ℕ × ℕ) := [(24, 5), (24, 6), (24, 5), (25, 5)]
private abbrev coordinateInput8_24 : LowerPair × Bool × Bool := (([3, 2], []), true, false)
private def coordinateCodes8_24 : List (ℕ × ℕ) := [(20, 1), (20, 2), (20, 1), (26, 1)]
private abbrev coordinateInput8_25 : LowerPair × Bool × Bool := (([3, 1], []), false, false)
private def coordinateCodes8_25 : List (ℕ × ℕ) := [(21, 5)]
private abbrev coordinateInput8_26 : LowerPair × Bool × Bool := (([3], [1]), true, true)
private def coordinateCodes8_26 : List (ℕ × ℕ) := [(19, 1), (19, 2), (19, 1), (20, 1)]
private abbrev coordinateInput8_27 : LowerPair × Bool × Bool := (([3], [2]), false, true)
private def coordinateCodes8_27 : List (ℕ × ℕ) := [(21, 6)]
private abbrev coordinateInput8_28 : LowerPair × Bool × Bool := (([3], [2]), true, true)
private def coordinateCodes8_28 : List (ℕ × ℕ) := [(19, 0), (19, 3), (19, 0), (20, 0)]
private abbrev coordinateInput8_29 : LowerPair × Bool × Bool := (([3], [1]), false, true)
private def coordinateCodes8_29 : List (ℕ × ℕ) := [(21, 4)]
private abbrev coordinateInput8_30 : LowerPair × Bool × Bool := (([], []), true, false)
private def coordinateCodes8_30 : List (ℕ × ℕ) := [(2, 1)]
private abbrev coordinateInput8_31 : LowerPair × Bool × Bool := (([], []), false, false)
private def coordinateCodes8_31 : List (ℕ × ℕ) := [(5, 5), (5, 6), (5, 5), (6, 5)]
private abbrev coordinateInput8_32 : LowerPair × Bool × Bool := (([3], [2]), true, false)
private def coordinateCodes8_32 : List (ℕ × ℕ) := [(19, 0), (19, 3), (19, 0), (20, 0)]
private abbrev coordinateInput8_33 : LowerPair × Bool × Bool := (([3], [2]), false, false)
private def coordinateCodes8_33 : List (ℕ × ℕ) := [(21, 6)]
private abbrev coordinateInput8_34 : LowerPair × Bool × Bool := (([3, 1], [2]), true, false)
private def coordinateCodes8_34 : List (ℕ × ℕ) := [(22, 0), (22, 3), (22, 0), (23, 0), (22, 0)]
private abbrev coordinateInput8_35 : LowerPair × Bool × Bool := (([3, 2], [2]), false, false)
private def coordinateCodes8_35 : List (ℕ × ℕ) := [(24, 6), (24, 6), (24, 8), (24, 6), (25, 6)]
private abbrev coordinateInput8_36 : LowerPair × Bool × Bool := (([3, 2], [2]), true, false)
private def coordinateCodes8_36 : List (ℕ × ℕ) := [(20, 0), (20, 3), (20, 0), (26, 0), (20, 0)]
private abbrev coordinateInput8_37 : LowerPair × Bool × Bool := (([3, 1], [2]), false, false)
private def coordinateCodes8_37 : List (ℕ × ℕ) := [(21, 6), (21, 6)]
private abbrev coordinateInput8_38 : LowerPair × Bool × Bool := (([3], [2, 1]), true, true)
private def coordinateCodes8_38 : List (ℕ × ℕ) := [(19, 14), (19, 14), (19, 15), (19, 14), (20, 14)]
private abbrev coordinateInput8_39 : LowerPair × Bool × Bool := (([3], [2, 2]), false, true)
private def coordinateCodes8_39 : List (ℕ × ℕ) := [(21, 16), (21, 16)]
private abbrev coordinateInput8_40 : LowerPair × Bool × Bool := (([3], [2, 2]), true, true)
private def coordinateCodes8_40 : List (ℕ × ℕ) := [(19, 3), (19, 3), (19, 18), (19, 3), (20, 3)]
private abbrev coordinateInput8_41 : LowerPair × Bool × Bool := (([3], [2, 1]), false, true)
private def coordinateCodes8_41 : List (ℕ × ℕ) := [(21, 6), (21, 6)]
private abbrev coordinateInput8_42 : LowerPair × Bool × Bool := (([3, 3], [3, 3]), true, false)
private def coordinateCodes8_42 : List (ℕ × ℕ) := [(27, 27)]
private abbrev coordinateInput8_43 : LowerPair × Bool × Bool := (([3, 3], [3, 3]), false, false)
private def coordinateCodes8_43 : List (ℕ × ℕ) := [(28, 28), (28, 29), (28, 28), (29, 28)]
private abbrev coordinateInput8_44 : LowerPair × Bool × Bool := (([3, 3, 1], [3, 3]), true, false)
private def coordinateCodes8_44 : List (ℕ × ℕ) := [(27, 27), (27, 27)]
private abbrev coordinateInput8_45 : LowerPair × Bool × Bool := (([3, 3, 2], [3, 3]), false, false)
private def coordinateCodes8_45 : List (ℕ × ℕ) := [(29, 28), (29, 29), (29, 28), (30, 28), (29, 28)]
private abbrev coordinateInput8_46 : LowerPair × Bool × Bool := (([3, 3, 2], [3, 3]), true, false)
private def coordinateCodes8_46 : List (ℕ × ℕ) := [(31, 27), (31, 27)]
private abbrev coordinateInput8_47 : LowerPair × Bool × Bool := (([3, 3, 1], [3, 3]), false, false)
private def coordinateCodes8_47 : List (ℕ × ℕ) := [(32, 28), (32, 29), (32, 28), (33, 28), (32, 28)]
private abbrev coordinateInput8_48 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 1]), true, true)
private def coordinateCodes8_48 : List (ℕ × ℕ) := [(27, 27), (27, 27)]
private abbrev coordinateInput8_49 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 2]), false, true)
private def coordinateCodes8_49 : List (ℕ × ℕ) := [(28, 29), (28, 29), (28, 30), (28, 29), (29, 29)]
private abbrev coordinateInput8_50 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 2]), true, true)
private def coordinateCodes8_50 : List (ℕ × ℕ) := [(27, 31), (27, 31)]
private abbrev coordinateInput8_51 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 1]), false, true)
private def coordinateCodes8_51 : List (ℕ × ℕ) := [(28, 32), (28, 32), (28, 33), (28, 32), (29, 32)]
private abbrev coordinateInput8_52 : LowerPair × Bool × Bool := (([3], [3]), true, false)
private def coordinateCodes8_52 : List (ℕ × ℕ) := [(19, 19), (19, 20), (19, 19), (20, 19)]
private abbrev coordinateInput8_53 : LowerPair × Bool × Bool := (([3], [3]), false, false)
private def coordinateCodes8_53 : List (ℕ × ℕ) := [(21, 21)]
private abbrev coordinateInput8_54 : LowerPair × Bool × Bool := (([3, 1], [3]), true, false)
private def coordinateCodes8_54 : List (ℕ × ℕ) := [(22, 19), (22, 20), (22, 19), (23, 19), (22, 19)]
private abbrev coordinateInput8_55 : LowerPair × Bool × Bool := (([3, 2], [3]), false, false)
private def coordinateCodes8_55 : List (ℕ × ℕ) := [(24, 21), (24, 21)]
private abbrev coordinateInput8_56 : LowerPair × Bool × Bool := (([3, 2], [3]), true, false)
private def coordinateCodes8_56 : List (ℕ × ℕ) := [(20, 19), (20, 20), (20, 19), (26, 19), (20, 19)]
private abbrev coordinateInput8_57 : LowerPair × Bool × Bool := (([3, 1], [3]), false, false)
private def coordinateCodes8_57 : List (ℕ × ℕ) := [(21, 21), (21, 21)]
private abbrev coordinateInput8_58 : LowerPair × Bool × Bool := (([3], [3, 1]), true, true)
private def coordinateCodes8_58 : List (ℕ × ℕ) := [(19, 22), (19, 22), (19, 23), (19, 22), (20, 22)]
private abbrev coordinateInput8_59 : LowerPair × Bool × Bool := (([3], [3, 2]), false, true)
private def coordinateCodes8_59 : List (ℕ × ℕ) := [(21, 24), (21, 24)]
private abbrev coordinateInput8_60 : LowerPair × Bool × Bool := (([3], [3, 2]), true, true)
private def coordinateCodes8_60 : List (ℕ × ℕ) := [(19, 20), (19, 20), (19, 26), (19, 20), (20, 20)]
private abbrev coordinateInput8_61 : LowerPair × Bool × Bool := (([3], [3, 1]), false, true)
private def coordinateCodes8_61 : List (ℕ × ℕ) := [(21, 21), (21, 21)]
private abbrev coordinateInput8_62 : LowerPair × Bool × Bool := (([2], [1]), true, false)
private def coordinateCodes8_62 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 1), (3, 1)]
private abbrev coordinateInput8_63 : LowerPair × Bool × Bool := (([2], [1]), false, false)
private def coordinateCodes8_63 : List (ℕ × ℕ) := [(6, 4), (6, 7), (6, 4), (8, 4)]
private abbrev coordinateInput8_64 : LowerPair × Bool × Bool := (([2, 1], [1]), true, false)
private def coordinateCodes8_64 : List (ℕ × ℕ) := [(14, 1), (14, 2), (14, 1), (15, 1), (14, 1)]
private abbrev coordinateInput8_65 : LowerPair × Bool × Bool := (([2, 2], [1]), false, false)
private def coordinateCodes8_65 : List (ℕ × ℕ) := [(16, 4), (16, 4), (16, 7), (16, 4), (17, 4)]
private abbrev coordinateInput8_66 : LowerPair × Bool × Bool := (([2, 2], [1]), true, false)
private def coordinateCodes8_66 : List (ℕ × ℕ) := [(3, 1), (3, 2), (3, 1), (18, 1), (3, 1)]
private abbrev coordinateInput8_67 : LowerPair × Bool × Bool := (([2, 1], [1]), false, false)
private def coordinateCodes8_67 : List (ℕ × ℕ) := [(6, 4), (6, 4), (6, 7), (6, 4), (8, 4)]
private abbrev coordinateInput8_68 : LowerPair × Bool × Bool := (([2], [1, 1]), true, true)
private def coordinateCodes8_68 : List (ℕ × ℕ) := [(0, 9), (0, 9), (0, 10), (0, 9), (3, 9)]
private abbrev coordinateInput8_69 : LowerPair × Bool × Bool := (([2], [1, 2]), false, true)
private def coordinateCodes8_69 : List (ℕ × ℕ) := [(6, 11), (6, 12), (6, 11), (8, 11), (6, 11)]
private abbrev coordinateInput8_70 : LowerPair × Bool × Bool := (([2], [1, 2]), true, true)
private def coordinateCodes8_70 : List (ℕ × ℕ) := [(0, 2), (0, 2), (0, 13), (0, 2), (3, 2)]
private abbrev coordinateInput8_71 : LowerPair × Bool × Bool := (([2], [1, 1]), false, true)
private def coordinateCodes8_71 : List (ℕ × ℕ) := [(6, 4), (6, 7), (6, 4), (8, 4), (6, 4)]
private abbrev coordinateInput8_72 : LowerPair × Bool × Bool := (([3], [1]), true, false)
private def coordinateCodes8_72 : List (ℕ × ℕ) := [(19, 1), (19, 2), (19, 1), (20, 1)]
private abbrev coordinateInput8_73 : LowerPair × Bool × Bool := (([3], [1]), false, false)
private def coordinateCodes8_73 : List (ℕ × ℕ) := [(21, 4)]
private abbrev coordinateInput8_74 : LowerPair × Bool × Bool := (([3, 1], [1]), true, false)
private def coordinateCodes8_74 : List (ℕ × ℕ) := [(22, 1), (22, 2), (22, 1), (23, 1), (22, 1)]
private abbrev coordinateInput8_75 : LowerPair × Bool × Bool := (([3, 2], [1]), false, false)
private def coordinateCodes8_75 : List (ℕ × ℕ) := [(24, 4), (24, 4), (24, 7), (24, 4), (25, 4)]
private abbrev coordinateInput8_76 : LowerPair × Bool × Bool := (([3, 2], [1]), true, false)
private def coordinateCodes8_76 : List (ℕ × ℕ) := [(20, 1), (20, 2), (20, 1), (26, 1), (20, 1)]
private abbrev coordinateInput8_77 : LowerPair × Bool × Bool := (([3, 1], [1]), false, false)
private def coordinateCodes8_77 : List (ℕ × ℕ) := [(21, 4), (21, 4)]
private abbrev coordinateInput8_78 : LowerPair × Bool × Bool := (([3], [1, 1]), true, true)
private def coordinateCodes8_78 : List (ℕ × ℕ) := [(19, 9), (19, 9), (19, 10), (19, 9), (20, 9)]
private abbrev coordinateInput8_79 : LowerPair × Bool × Bool := (([3], [1, 2]), false, true)
private def coordinateCodes8_79 : List (ℕ × ℕ) := [(21, 11), (21, 11)]
private abbrev coordinateInput8_80 : LowerPair × Bool × Bool := (([3], [1, 2]), true, true)
private def coordinateCodes8_80 : List (ℕ × ℕ) := [(19, 2), (19, 2), (19, 13), (19, 2), (20, 2)]
private abbrev coordinateInput8_81 : LowerPair × Bool × Bool := (([3], [1, 1]), false, true)
private def coordinateCodes8_81 : List (ℕ × ℕ) := [(21, 4), (21, 4)]
private abbrev coordinateInput8_82 : LowerPair × Bool × Bool := (([2], [2]), true, false)
private def coordinateCodes8_82 : List (ℕ × ℕ) := [(0, 0), (0, 3), (0, 0), (3, 0)]
private abbrev coordinateInput8_83 : LowerPair × Bool × Bool := (([2], [2]), false, false)
private def coordinateCodes8_83 : List (ℕ × ℕ) := [(6, 6), (6, 8), (6, 6), (8, 6)]
private abbrev coordinateInput8_84 : LowerPair × Bool × Bool := (([2, 1], [2]), true, false)
private def coordinateCodes8_84 : List (ℕ × ℕ) := [(14, 0), (14, 3), (14, 0), (15, 0), (14, 0)]
private abbrev coordinateInput8_85 : LowerPair × Bool × Bool := (([2, 2], [2]), false, false)
private def coordinateCodes8_85 : List (ℕ × ℕ) := [(16, 6), (16, 6), (16, 8), (16, 6), (17, 6)]
private abbrev coordinateInput8_86 : LowerPair × Bool × Bool := (([2, 2], [2]), true, false)
private def coordinateCodes8_86 : List (ℕ × ℕ) := [(3, 0), (3, 3), (3, 0), (18, 0), (3, 0)]
private abbrev coordinateInput8_87 : LowerPair × Bool × Bool := (([2, 1], [2]), false, false)
private def coordinateCodes8_87 : List (ℕ × ℕ) := [(6, 6), (6, 6), (6, 8), (6, 6), (8, 6)]
private abbrev coordinateInput8_88 : LowerPair × Bool × Bool := (([2], [2, 1]), true, true)
private def coordinateCodes8_88 : List (ℕ × ℕ) := [(0, 14), (0, 14), (0, 15), (0, 14), (3, 14)]
private abbrev coordinateInput8_89 : LowerPair × Bool × Bool := (([2], [2, 2]), false, true)
private def coordinateCodes8_89 : List (ℕ × ℕ) := [(6, 16), (6, 17), (6, 16), (8, 16), (6, 16)]
private abbrev coordinateInput8_90 : LowerPair × Bool × Bool := (([2], [2, 2]), true, true)
private def coordinateCodes8_90 : List (ℕ × ℕ) := [(0, 3), (0, 3), (0, 18), (0, 3), (3, 3)]
private abbrev coordinateInput8_91 : LowerPair × Bool × Bool := (([2], [2, 1]), false, true)
private def coordinateCodes8_91 : List (ℕ × ℕ) := [(6, 6), (6, 8), (6, 6), (8, 6), (6, 6)]
private abbrev coordinateInput8_92 : LowerPair × Bool × Bool := (([2], [3]), true, false)
private def coordinateCodes8_92 : List (ℕ × ℕ) := [(0, 19), (0, 20), (0, 19), (3, 19)]
private abbrev coordinateInput8_93 : LowerPair × Bool × Bool := (([2], [3]), false, false)
private def coordinateCodes8_93 : List (ℕ × ℕ) := [(6, 21)]
private abbrev coordinateInput8_94 : LowerPair × Bool × Bool := (([2, 1], [3]), true, false)
private def coordinateCodes8_94 : List (ℕ × ℕ) := [(14, 19), (14, 20), (14, 19), (15, 19), (14, 19)]
private abbrev coordinateInput8_95 : LowerPair × Bool × Bool := (([2, 2], [3]), false, false)
private def coordinateCodes8_95 : List (ℕ × ℕ) := [(16, 21), (16, 21)]
private abbrev coordinateInput8_96 : LowerPair × Bool × Bool := (([2, 2], [3]), true, false)
private def coordinateCodes8_96 : List (ℕ × ℕ) := [(3, 19), (3, 20), (3, 19), (18, 19), (3, 19)]
private abbrev coordinateInput8_97 : LowerPair × Bool × Bool := (([2, 1], [3]), false, false)
private def coordinateCodes8_97 : List (ℕ × ℕ) := [(6, 21), (6, 21)]
private abbrev coordinateInput8_98 : LowerPair × Bool × Bool := (([2], [3, 1]), true, true)
private def coordinateCodes8_98 : List (ℕ × ℕ) := [(0, 22), (0, 22), (0, 23), (0, 22), (3, 22)]
private abbrev coordinateInput8_99 : LowerPair × Bool × Bool := (([2], [3, 2]), false, true)
private def coordinateCodes8_99 : List (ℕ × ℕ) := [(6, 24), (6, 25), (6, 24), (8, 24), (6, 24)]
private abbrev coordinateInput8_100 : LowerPair × Bool × Bool := (([2], [3, 2]), true, true)
private def coordinateCodes8_100 : List (ℕ × ℕ) := [(0, 20), (0, 20), (0, 26), (0, 20), (3, 20)]
private abbrev coordinateInput8_101 : LowerPair × Bool × Bool := (([2], [3, 1]), false, true)
private def coordinateCodes8_101 : List (ℕ × ℕ) := [(6, 21), (6, 21)]
private abbrev coordinateInput8_102 : LowerPair × Bool × Bool := (([3], [1, 1]), true, false)
private def coordinateCodes8_102 : List (ℕ × ℕ) := [(19, 9), (19, 9), (19, 10), (19, 9), (20, 9)]
private abbrev coordinateInput8_103 : LowerPair × Bool × Bool := (([3], [1, 1]), false, false)
private def coordinateCodes8_103 : List (ℕ × ℕ) := [(21, 4), (21, 4)]
private abbrev coordinateInput8_104 : LowerPair × Bool × Bool := (([3, 1], [1, 1]), true, false)
private def coordinateCodes8_104 : List (ℕ × ℕ) := [(22, 9), (22, 10), (22, 9), (23, 9)]
private abbrev coordinateInput8_105 : LowerPair × Bool × Bool := (([3, 2], [1, 1]), false, false)
private def coordinateCodes8_105 : List (ℕ × ℕ) := [(24, 4), (24, 7), (24, 4), (25, 4)]
private abbrev coordinateInput8_106 : LowerPair × Bool × Bool := (([3, 2], [1, 1]), true, false)
private def coordinateCodes8_106 : List (ℕ × ℕ) := [(20, 9), (20, 10), (20, 9), (26, 9)]
private abbrev coordinateInput8_107 : LowerPair × Bool × Bool := (([3, 1], [1, 1]), false, false)
private def coordinateCodes8_107 : List (ℕ × ℕ) := [(21, 4)]
private abbrev coordinateInput8_108 : LowerPair × Bool × Bool := (([3], [1, 1, 1]), true, true)
private def coordinateCodes8_108 : List (ℕ × ℕ) := [(19, 9), (19, 10), (19, 9), (20, 9)]
private abbrev coordinateInput8_109 : LowerPair × Bool × Bool := (([3], [1, 1, 2]), false, true)
private def coordinateCodes8_109 : List (ℕ × ℕ) := [(21, 7)]
private abbrev coordinateInput8_110 : LowerPair × Bool × Bool := (([3], [1, 1, 2]), true, true)
private def coordinateCodes8_110 : List (ℕ × ℕ) := [(19, 34), (19, 35), (19, 34), (20, 34)]
private abbrev coordinateInput8_111 : LowerPair × Bool × Bool := (([3], [1, 1, 1]), false, true)
private def coordinateCodes8_111 : List (ℕ × ℕ) := [(21, 36)]

private def decodeCoordinate8 (x : ℕ × ℕ) : CertField × CertField :=
  (coordinateFields8[x.1]?.getD ⟨0,0,0,0⟩,coordinateFields8[x.2]?.getD ⟨0,0,0,0⟩)

private theorem hCoordinate8_0 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_0.1 coordinateInput8_0.2.1 coordinateInput8_0.2.2).map Prod.fst = coordinateCodes8_0.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_1 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_1.1 coordinateInput8_1.2.1 coordinateInput8_1.2.2).map Prod.fst = coordinateCodes8_1.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_2 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_2.1 coordinateInput8_2.2.1 coordinateInput8_2.2.2).map Prod.fst = coordinateCodes8_2.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_3 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_3.1 coordinateInput8_3.2.1 coordinateInput8_3.2.2).map Prod.fst = coordinateCodes8_3.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_4 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_4.1 coordinateInput8_4.2.1 coordinateInput8_4.2.2).map Prod.fst = coordinateCodes8_4.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_5 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_5.1 coordinateInput8_5.2.1 coordinateInput8_5.2.2).map Prod.fst = coordinateCodes8_5.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_6 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_6.1 coordinateInput8_6.2.1 coordinateInput8_6.2.2).map Prod.fst = coordinateCodes8_6.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_7 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_7.1 coordinateInput8_7.2.1 coordinateInput8_7.2.2).map Prod.fst = coordinateCodes8_7.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_8 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_8.1 coordinateInput8_8.2.1 coordinateInput8_8.2.2).map Prod.fst = coordinateCodes8_8.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_9 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_9.1 coordinateInput8_9.2.1 coordinateInput8_9.2.2).map Prod.fst = coordinateCodes8_9.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_10 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_10.1 coordinateInput8_10.2.1 coordinateInput8_10.2.2).map Prod.fst = coordinateCodes8_10.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_11 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_11.1 coordinateInput8_11.2.1 coordinateInput8_11.2.2).map Prod.fst = coordinateCodes8_11.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_12 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_12.1 coordinateInput8_12.2.1 coordinateInput8_12.2.2).map Prod.fst = coordinateCodes8_12.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_13 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_13.1 coordinateInput8_13.2.1 coordinateInput8_13.2.2).map Prod.fst = coordinateCodes8_13.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_14 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_14.1 coordinateInput8_14.2.1 coordinateInput8_14.2.2).map Prod.fst = coordinateCodes8_14.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_15 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_15.1 coordinateInput8_15.2.1 coordinateInput8_15.2.2).map Prod.fst = coordinateCodes8_15.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_16 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_16.1 coordinateInput8_16.2.1 coordinateInput8_16.2.2).map Prod.fst = coordinateCodes8_16.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_17 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_17.1 coordinateInput8_17.2.1 coordinateInput8_17.2.2).map Prod.fst = coordinateCodes8_17.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_18 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_18.1 coordinateInput8_18.2.1 coordinateInput8_18.2.2).map Prod.fst = coordinateCodes8_18.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_19 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_19.1 coordinateInput8_19.2.1 coordinateInput8_19.2.2).map Prod.fst = coordinateCodes8_19.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_20 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_20.1 coordinateInput8_20.2.1 coordinateInput8_20.2.2).map Prod.fst = coordinateCodes8_20.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_21 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_21.1 coordinateInput8_21.2.1 coordinateInput8_21.2.2).map Prod.fst = coordinateCodes8_21.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_22 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_22.1 coordinateInput8_22.2.1 coordinateInput8_22.2.2).map Prod.fst = coordinateCodes8_22.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_23 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_23.1 coordinateInput8_23.2.1 coordinateInput8_23.2.2).map Prod.fst = coordinateCodes8_23.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_24 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_24.1 coordinateInput8_24.2.1 coordinateInput8_24.2.2).map Prod.fst = coordinateCodes8_24.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_25 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_25.1 coordinateInput8_25.2.1 coordinateInput8_25.2.2).map Prod.fst = coordinateCodes8_25.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_26 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_26.1 coordinateInput8_26.2.1 coordinateInput8_26.2.2).map Prod.fst = coordinateCodes8_26.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_27 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_27.1 coordinateInput8_27.2.1 coordinateInput8_27.2.2).map Prod.fst = coordinateCodes8_27.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_28 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_28.1 coordinateInput8_28.2.1 coordinateInput8_28.2.2).map Prod.fst = coordinateCodes8_28.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_29 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_29.1 coordinateInput8_29.2.1 coordinateInput8_29.2.2).map Prod.fst = coordinateCodes8_29.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_30 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_30.1 coordinateInput8_30.2.1 coordinateInput8_30.2.2).map Prod.fst = coordinateCodes8_30.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_31 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_31.1 coordinateInput8_31.2.1 coordinateInput8_31.2.2).map Prod.fst = coordinateCodes8_31.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_32 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_32.1 coordinateInput8_32.2.1 coordinateInput8_32.2.2).map Prod.fst = coordinateCodes8_32.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_33 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_33.1 coordinateInput8_33.2.1 coordinateInput8_33.2.2).map Prod.fst = coordinateCodes8_33.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_34 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_34.1 coordinateInput8_34.2.1 coordinateInput8_34.2.2).map Prod.fst = coordinateCodes8_34.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_35 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_35.1 coordinateInput8_35.2.1 coordinateInput8_35.2.2).map Prod.fst = coordinateCodes8_35.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_36 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_36.1 coordinateInput8_36.2.1 coordinateInput8_36.2.2).map Prod.fst = coordinateCodes8_36.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_37 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_37.1 coordinateInput8_37.2.1 coordinateInput8_37.2.2).map Prod.fst = coordinateCodes8_37.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_38 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_38.1 coordinateInput8_38.2.1 coordinateInput8_38.2.2).map Prod.fst = coordinateCodes8_38.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_39 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_39.1 coordinateInput8_39.2.1 coordinateInput8_39.2.2).map Prod.fst = coordinateCodes8_39.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_40 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_40.1 coordinateInput8_40.2.1 coordinateInput8_40.2.2).map Prod.fst = coordinateCodes8_40.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_41 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_41.1 coordinateInput8_41.2.1 coordinateInput8_41.2.2).map Prod.fst = coordinateCodes8_41.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_42 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_42.1 coordinateInput8_42.2.1 coordinateInput8_42.2.2).map Prod.fst = coordinateCodes8_42.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_43 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_43.1 coordinateInput8_43.2.1 coordinateInput8_43.2.2).map Prod.fst = coordinateCodes8_43.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_44 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_44.1 coordinateInput8_44.2.1 coordinateInput8_44.2.2).map Prod.fst = coordinateCodes8_44.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_45 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_45.1 coordinateInput8_45.2.1 coordinateInput8_45.2.2).map Prod.fst = coordinateCodes8_45.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_46 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_46.1 coordinateInput8_46.2.1 coordinateInput8_46.2.2).map Prod.fst = coordinateCodes8_46.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_47 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_47.1 coordinateInput8_47.2.1 coordinateInput8_47.2.2).map Prod.fst = coordinateCodes8_47.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_48 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_48.1 coordinateInput8_48.2.1 coordinateInput8_48.2.2).map Prod.fst = coordinateCodes8_48.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_49 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_49.1 coordinateInput8_49.2.1 coordinateInput8_49.2.2).map Prod.fst = coordinateCodes8_49.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_50 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_50.1 coordinateInput8_50.2.1 coordinateInput8_50.2.2).map Prod.fst = coordinateCodes8_50.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_51 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_51.1 coordinateInput8_51.2.1 coordinateInput8_51.2.2).map Prod.fst = coordinateCodes8_51.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_52 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_52.1 coordinateInput8_52.2.1 coordinateInput8_52.2.2).map Prod.fst = coordinateCodes8_52.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_53 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_53.1 coordinateInput8_53.2.1 coordinateInput8_53.2.2).map Prod.fst = coordinateCodes8_53.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_54 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_54.1 coordinateInput8_54.2.1 coordinateInput8_54.2.2).map Prod.fst = coordinateCodes8_54.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_55 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_55.1 coordinateInput8_55.2.1 coordinateInput8_55.2.2).map Prod.fst = coordinateCodes8_55.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_56 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_56.1 coordinateInput8_56.2.1 coordinateInput8_56.2.2).map Prod.fst = coordinateCodes8_56.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_57 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_57.1 coordinateInput8_57.2.1 coordinateInput8_57.2.2).map Prod.fst = coordinateCodes8_57.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_58 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_58.1 coordinateInput8_58.2.1 coordinateInput8_58.2.2).map Prod.fst = coordinateCodes8_58.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_59 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_59.1 coordinateInput8_59.2.1 coordinateInput8_59.2.2).map Prod.fst = coordinateCodes8_59.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_60 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_60.1 coordinateInput8_60.2.1 coordinateInput8_60.2.2).map Prod.fst = coordinateCodes8_60.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_61 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_61.1 coordinateInput8_61.2.1 coordinateInput8_61.2.2).map Prod.fst = coordinateCodes8_61.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_62 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_62.1 coordinateInput8_62.2.1 coordinateInput8_62.2.2).map Prod.fst = coordinateCodes8_62.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_63 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_63.1 coordinateInput8_63.2.1 coordinateInput8_63.2.2).map Prod.fst = coordinateCodes8_63.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_64 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_64.1 coordinateInput8_64.2.1 coordinateInput8_64.2.2).map Prod.fst = coordinateCodes8_64.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_65 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_65.1 coordinateInput8_65.2.1 coordinateInput8_65.2.2).map Prod.fst = coordinateCodes8_65.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_66 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_66.1 coordinateInput8_66.2.1 coordinateInput8_66.2.2).map Prod.fst = coordinateCodes8_66.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_67 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_67.1 coordinateInput8_67.2.1 coordinateInput8_67.2.2).map Prod.fst = coordinateCodes8_67.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_68 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_68.1 coordinateInput8_68.2.1 coordinateInput8_68.2.2).map Prod.fst = coordinateCodes8_68.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_69 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_69.1 coordinateInput8_69.2.1 coordinateInput8_69.2.2).map Prod.fst = coordinateCodes8_69.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_70 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_70.1 coordinateInput8_70.2.1 coordinateInput8_70.2.2).map Prod.fst = coordinateCodes8_70.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_71 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_71.1 coordinateInput8_71.2.1 coordinateInput8_71.2.2).map Prod.fst = coordinateCodes8_71.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_72 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_72.1 coordinateInput8_72.2.1 coordinateInput8_72.2.2).map Prod.fst = coordinateCodes8_72.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_73 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_73.1 coordinateInput8_73.2.1 coordinateInput8_73.2.2).map Prod.fst = coordinateCodes8_73.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_74 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_74.1 coordinateInput8_74.2.1 coordinateInput8_74.2.2).map Prod.fst = coordinateCodes8_74.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_75 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_75.1 coordinateInput8_75.2.1 coordinateInput8_75.2.2).map Prod.fst = coordinateCodes8_75.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_76 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_76.1 coordinateInput8_76.2.1 coordinateInput8_76.2.2).map Prod.fst = coordinateCodes8_76.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_77 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_77.1 coordinateInput8_77.2.1 coordinateInput8_77.2.2).map Prod.fst = coordinateCodes8_77.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_78 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_78.1 coordinateInput8_78.2.1 coordinateInput8_78.2.2).map Prod.fst = coordinateCodes8_78.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_79 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_79.1 coordinateInput8_79.2.1 coordinateInput8_79.2.2).map Prod.fst = coordinateCodes8_79.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_80 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_80.1 coordinateInput8_80.2.1 coordinateInput8_80.2.2).map Prod.fst = coordinateCodes8_80.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_81 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_81.1 coordinateInput8_81.2.1 coordinateInput8_81.2.2).map Prod.fst = coordinateCodes8_81.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_82 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_82.1 coordinateInput8_82.2.1 coordinateInput8_82.2.2).map Prod.fst = coordinateCodes8_82.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_83 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_83.1 coordinateInput8_83.2.1 coordinateInput8_83.2.2).map Prod.fst = coordinateCodes8_83.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_84 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_84.1 coordinateInput8_84.2.1 coordinateInput8_84.2.2).map Prod.fst = coordinateCodes8_84.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_85 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_85.1 coordinateInput8_85.2.1 coordinateInput8_85.2.2).map Prod.fst = coordinateCodes8_85.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_86 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_86.1 coordinateInput8_86.2.1 coordinateInput8_86.2.2).map Prod.fst = coordinateCodes8_86.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_87 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_87.1 coordinateInput8_87.2.1 coordinateInput8_87.2.2).map Prod.fst = coordinateCodes8_87.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_88 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_88.1 coordinateInput8_88.2.1 coordinateInput8_88.2.2).map Prod.fst = coordinateCodes8_88.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_89 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_89.1 coordinateInput8_89.2.1 coordinateInput8_89.2.2).map Prod.fst = coordinateCodes8_89.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_90 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_90.1 coordinateInput8_90.2.1 coordinateInput8_90.2.2).map Prod.fst = coordinateCodes8_90.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_91 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_91.1 coordinateInput8_91.2.1 coordinateInput8_91.2.2).map Prod.fst = coordinateCodes8_91.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_92 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_92.1 coordinateInput8_92.2.1 coordinateInput8_92.2.2).map Prod.fst = coordinateCodes8_92.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_93 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_93.1 coordinateInput8_93.2.1 coordinateInput8_93.2.2).map Prod.fst = coordinateCodes8_93.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_94 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_94.1 coordinateInput8_94.2.1 coordinateInput8_94.2.2).map Prod.fst = coordinateCodes8_94.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_95 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_95.1 coordinateInput8_95.2.1 coordinateInput8_95.2.2).map Prod.fst = coordinateCodes8_95.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_96 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_96.1 coordinateInput8_96.2.1 coordinateInput8_96.2.2).map Prod.fst = coordinateCodes8_96.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_97 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_97.1 coordinateInput8_97.2.1 coordinateInput8_97.2.2).map Prod.fst = coordinateCodes8_97.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_98 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_98.1 coordinateInput8_98.2.1 coordinateInput8_98.2.2).map Prod.fst = coordinateCodes8_98.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_99 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_99.1 coordinateInput8_99.2.1 coordinateInput8_99.2.2).map Prod.fst = coordinateCodes8_99.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_100 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_100.1 coordinateInput8_100.2.1 coordinateInput8_100.2.2).map Prod.fst = coordinateCodes8_100.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_101 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_101.1 coordinateInput8_101.2.1 coordinateInput8_101.2.2).map Prod.fst = coordinateCodes8_101.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_102 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_102.1 coordinateInput8_102.2.1 coordinateInput8_102.2.2).map Prod.fst = coordinateCodes8_102.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_103 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_103.1 coordinateInput8_103.2.1 coordinateInput8_103.2.2).map Prod.fst = coordinateCodes8_103.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_104 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_104.1 coordinateInput8_104.2.1 coordinateInput8_104.2.2).map Prod.fst = coordinateCodes8_104.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_105 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_105.1 coordinateInput8_105.2.1 coordinateInput8_105.2.2).map Prod.fst = coordinateCodes8_105.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_106 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_106.1 coordinateInput8_106.2.1 coordinateInput8_106.2.2).map Prod.fst = coordinateCodes8_106.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_107 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_107.1 coordinateInput8_107.2.1 coordinateInput8_107.2.2).map Prod.fst = coordinateCodes8_107.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_108 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_108.1 coordinateInput8_108.2.1 coordinateInput8_108.2.2).map Prod.fst = coordinateCodes8_108.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_109 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_109.1 coordinateInput8_109.2.1 coordinateInput8_109.2.2).map Prod.fst = coordinateCodes8_109.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_110 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_110.1 coordinateInput8_110.2.1 coordinateInput8_110.2.2).map Prod.fst = coordinateCodes8_110.map decodeCoordinate8 := by decide +kernel

private theorem hCoordinate8_111 :
    (trunkEndpointCases (trunkCatalog.states 8).context coordinateInput8_111.1 coordinateInput8_111.2.1 coordinateInput8_111.2.2).map Prod.fst = coordinateCodes8_111.map decodeCoordinate8 := by decide +kernel

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
(0,[4,14,24,34,44,49,50,51,52,53,60,61,62,63,70,71,72,73,80,81,82,83,95,96,97,98,100,101,102,103,110,111,112,113,120,121,122,123,130,131,132,133,145,146,147,148,150,151,152,153,160,161,162,163,170,171,172,173,180,181,182,183,190,191,192,193,195,196,197,198,200,201,202,203,210,211,212,213,220,221,222,223,230,231,232,233,240,241,242,243,245,246,247,248],0,[-1]),
(0,[5,6,7,8,9,15,16,17,18,19,25,26,27,28,29,35,36,37,38,39,40,41,42,43,55,56,57,58,59,65,66,67,68,69,75,76,77,78,79,85,86,87,88,89,90,91,92,93,94,105,106,107,108,109,115,116,117,118,119,125,126,127,128,129,135,136,137,138,139,140,141,142,143,144,155,156,157,158,159,165,166,167,168,169,175,176,177,178,179,185,186,187,188,189,194,205,206,207,208,209,215,216,217,218,219,225,226,227,228,229,235,236,237,238,239,244],0,[-1]),
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
(0,[74],2,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[74,124],5,[0,1,2,3]),
(0,[74,124],7,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[74],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[74],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[74],15,[0,1,2,3]),
(0,[74],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(0,[74],19,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(0,[84],0,[-1]),
(0,[99],0,[-1]),
(0,[104],0,[-1]),
(0,[114],0,[-1]),
(0,[124],2,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[124],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[124],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[124],15,[0,1,2,3]),
(0,[124],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(0,[124],19,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(0,[134],0,[-1]),
(0,[149],0,[-1]),
(0,[154],0,[-1]),
(0,[164],0,[-1]),
(0,[174,199],0,[-1]),
(0,[184],0,[-1]),
(0,[204],0,[-1]),
(0,[214],0,[-1]),
(0,[224,249],0,[-1]),
(0,[234],0,[-1]),
(1,[0,10,20,30,45],0,[-1]),
(1,[1,11,21,31,46],0,[-1]),
(1,[2,54,104,154,204],0,[-1]),
(1,[3,13,23,33,48],0,[-1]),
(1,[4,14,24,34,49,50,51,52,53,60,61,62,63,70,71,72,73,80,81,82,83,95,96,97,98,100,101,102,103,110,111,112,113,120,121,122,123,130,131,132,133,145,146,147,148,150,151,152,153,160,161,162,163,170,171,172,173,180,181,182,183,190,191,192,193,195,196,197,198,200,201,202,203,210,211,212,213,220,221,222,223,230,231,232,233,240,241,242,243,245,246,247,248],0,[-1]),
(1,[5,6,7,8,9,15,16,17,18,19,25,26,27,28,29,35,36,37,38,39,40,41,42,43,44,55,56,57,58,59,65,66,67,68,69,75,76,77,78,79,85,86,87,88,89,90,91,92,93,94,105,106,107,108,109,115,116,117,118,119,125,126,127,128,129,135,136,137,138,139,140,141,142,143,144,155,156,157,158,159,165,166,167,168,169,175,176,177,178,179,185,186,187,188,189,194,205,206,207,208,209,215,216,217,218,219,225,226,227,228,229,235,236,237,238,239,244],0,[-1]),
(1,[12,64,114,164,214],0,[-1]),
(1,[22,32,47],0,[-1]),
(1,[74,99],0,[-1]),
(1,[84,134,184,234],0,[-1]),
(1,[124,174,224],0,[-1]),
(1,[149],0,[-1]),
(1,[199,249],2,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(1,[199],5,[0,1,2,3]),
(1,[199,249],7,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(1,[199],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(1,[199,249],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(1,[199],14,[0,1,2,3,4,5,6,7,8,9]),
(1,[199],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(1,[199,249],19,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]),
(1,[199,249],21,[0,2,3]),
(1,[249],5,[0,1,2,3]),
(1,[249],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(1,[249],14,[0,1,2,3,4,5,6,7,8,9]),
(1,[249],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[0,10,20,30],0,[-1]),
(2,[1,11,21,31],0,[-1]),
(2,[2,54,104],0,[-1]),
(2,[3,13,23,33],0,[-1]),
(2,[4,14,24,34,49,50,51,52,53,60,61,62,63,70,71,72,73,80,81,82,83,95,96,97,98,100,101,102,103,110,111,112,113,120,121,122,123,130,131,132,133,145,146,147,148,150,151,152,153,160,161,162,163,170,171,172,173,180,181,182,183,190,191,192,193,195,196,197,198,200,201,202,203,210,211,212,213,220,221,222,223,230,231,232,233,240,241,242,243,245,246,247,248],0,[-1]),
(2,[5,6,7,8,9,15,16,17,18,19,25,26,27,28,29,35,36,37,38,39,40,41,42,43,44,55,56,57,58,59,65,66,67,68,69,75,76,77,78,79,85,86,87,88,89,90,91,92,93,94,105,106,107,108,109,115,116,117,118,119,125,126,127,128,129,135,136,137,138,139,140,141,142,143,144,155,156,157,158,159,165,166,167,168,169,175,176,177,178,179,185,186,187,188,189,194,205,206,207,208,209,215,216,217,218,219,225,226,227,228,229,235,236,237,238,239,244],0,[-1]),
(2,[12,64,114],0,[-1]),
(2,[22,32],0,[-1]),
(2,[45],0,[-1]),
(2,[46],0,[-1]),
(2,[47],0,[-1]),
(2,[48],0,[-1]),
(2,[74],0,[-1]),
(2,[84,134],0,[-1]),
(2,[99],0,[-1]),
(2,[124],2,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[124],5,[0,1,2,3]),
(2,[124,149,199,249],7,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[124],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[124],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[124],14,[0,1,2,3,4,5,6,7,8,9]),
(2,[124],18,[0,1,2,3,4,5,6,7,8,9]),
(2,[124],20,[0,1,2,3,4,5,6,7,8,9]),
(2,[124],22,[0,1,2,3,4,5,6,7,8,9]),
(2,[124],24,[0,1,2,3,4,5,6,7,8,9]),
(2,[124],27,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[124],29,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]),
(2,[124,149,249],30,[12,13,14,15]),
(2,[124],31,[0]),
(2,[149,199,249],2,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[149],5,[0,1,2,3]),
(2,[149],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[149],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[149],14,[0,1,2,3,4,5,6,7,8,9]),
(2,[149],18,[0,1,2,3,4,5,6,7,8,9]),
(2,[149],20,[0,1,2,3,4,5,6,7,8,9]),
(2,[149],22,[0,1,2,3,4,5,6,7,8,9]),
(2,[149],24,[0,1,2,3,4,5,6,7,8,9]),
(2,[149],27,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[149],29,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]),
(2,[149],31,[0]),
(2,[154],0,[-1]),
(2,[164],0,[-1]),
(2,[174],0,[-1]),
(2,[184],0,[-1]),
(2,[199],5,[0,1,2,3]),
(2,[199],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[199],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[199],14,[0,1,2,3,4,5,6,7,8,9]),
(2,[199],18,[0,1,2,3,4,5,6,7,8,9]),
(2,[199],20,[0,1,2,3,4,5,6,7,8,9]),
(2,[199],22,[0,1,2,3,4,5,6,7,8,9]),
(2,[199],24,[0,1,2,3,4,5,6,7,8,9]),
(2,[199],27,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[199],29,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]),
(2,[199],30,[12,13,14,15]),
(2,[199],31,[0]),
(2,[204],0,[-1]),
(2,[214],0,[-1]),
(2,[224],0,[-1]),
(2,[234],0,[-1]),
(2,[249],5,[0,1,2,3]),
(2,[249],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[249],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[249],14,[0,1,2,3,4,5,6,7,8,9]),
(2,[249],18,[0,1,2,3,4,5,6,7,8,9]),
(2,[249],20,[0,1,2,3,4,5,6,7,8,9]),
(2,[249],22,[0,1,2,3,4,5,6,7,8,9]),
(2,[249],24,[0,1,2,3,4,5,6,7,8,9]),
(2,[249],27,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[249],29,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]),
(2,[249],31,[0]),
(3,[0,10,20,30,45],0,[-1]),
(3,[1,11,21,31,46],0,[-1]),
(3,[2,54,104,154,204],0,[-1]),
(3,[3,13,23,33,48],0,[-1]),
(3,[4,14,24,34,49,50,51,52,53,60,61,62,63,70,71,72,73,80,81,82,83,95,96,97,98,100,101,102,103,110,111,112,113,120,121,122,123,130,131,132,133,145,146,147,148,150,151,152,153,160,161,162,163,170,171,172,173,180,181,182,183,190,191,192,193,195,196,197,198,200,201,202,203,210,211,212,213,220,221,222,223,230,231,232,233,240,241,242,243,245,246,247,248],0,[-1]),
(3,[5,6,7,8,9,15,16,17,18,19,25,26,27,28,29,35,36,37,38,39,40,41,42,43,44,55,56,57,58,59,65,66,67,68,69,75,76,77,78,79,85,86,87,88,89,90,91,92,93,94,105,106,107,108,109,115,116,117,118,119,125,126,127,128,129,135,136,137,138,139,140,141,142,143,144,155,156,157,158,159,165,166,167,168,169,175,176,177,178,179,185,186,187,188,189,194,205,206,207,208,209,215,216,217,218,219,225,226,227,228,229,235,236,237,238,239,244],0,[-1]),
(3,[12,64,114,164,214],0,[-1]),
(3,[22,32,47],0,[-1]),
(3,[74,99],0,[-1]),
(3,[84,134,184,234],0,[-1]),
(3,[124,174,224],0,[-1]),
(3,[149],0,[-1]),
(3,[199],2,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[199],5,[0,1,2,3]),
(3,[199],7,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[199],9,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[199],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[199],14,[0,1,2,3,4,5,6,7,8,9]),
(3,[199],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[199],19,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[199],22,[0,1,2,3,4,5,6,7,8,9]),
(3,[199],24,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[199],27,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(3,[199],29,[0,1,2,3,4,5,6,7,8,9]),
(3,[199],32,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]),
(3,[199],34,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[199],35,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[199],36,[0,1,2,3]),
(3,[199],38,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(3,[199],39,[0,1,2,3]),
(3,[199],40,[0,1,2,3]),
(3,[199],42,[0,2,3]),
(3,[249],0,[-1]),
(4,[0,10,20,30,45],0,[-1]),
(4,[1,11,21,31,46],0,[-1]),
(4,[2,54,104,154,204],0,[-1]),
(4,[3,13,23,33,48],0,[-1]),
(4,[4,14,24,34,49,50,51,52,53,60,61,62,63,70,71,72,73,80,81,82,83,95,96,97,98,100,101,102,103,110,111,112,113,120,121,122,123,130,131,132,133,145,146,147,148,150,151,152,153,160,161,162,163,170,171,172,173,180,181,182,183,190,191,192,193,195,196,197,198,200,201,202,203,210,211,212,213,220,221,222,223,230,231,232,233,240,241,242,243,245,246,247,248],0,[-1]),
(4,[5,6,7,8,9,15,16,17,18,19,25,26,27,28,29,35,36,37,38,39,40,41,42,43,44,55,56,57,58,59,65,66,67,68,69,75,76,77,78,79,85,86,87,88,89,90,91,92,93,94,105,106,107,108,109,115,116,117,118,119,125,126,127,128,129,135,136,137,138,139,140,141,142,143,144,155,156,157,158,159,165,166,167,168,169,175,176,177,178,179,185,186,187,188,189,194,205,206,207,208,209,215,216,217,218,219,225,226,227,228,229,235,236,237,238,239,244],0,[-1]),
(4,[12,64,114,164,214],0,[-1]),
(4,[22,32,47],0,[-1]),
(4,[74,99],0,[-1]),
(4,[84,134,184,234],0,[-1]),
(4,[124,174,224],0,[-1]),
(4,[149],0,[-1]),
(4,[199],2,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(4,[199],5,[0,1,2,3]),
(4,[199],7,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[199],9,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[199],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[199],14,[0,1,2,3,4,5,6,7,8,9]),
(4,[199],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[199],19,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[199],22,[0,1,2,3,4,5,6,7,8,9]),
(4,[199],24,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[199],27,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(4,[199],29,[0,1,2,3,4,5,6,7,8,9]),
(4,[199],33,[0,1,2,3,4,5,6,7,8,9]),
(4,[199],35,[0,1,2,3,4,5,6,7,8,9]),
(4,[199],37,[0,1,2,3,4,5,6,7,8,9]),
(4,[199],39,[0,1,2,3,4,5,6,7,8,9]),
(4,[199],42,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]),
(4,[199],44,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(4,[199],45,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(4,[199],46,[0,1,2,3]),
(4,[199],48,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(4,[199],49,[0,1,2,3]),
(4,[199],50,[0,1,2,3]),
(4,[199],51,[12,13,14,15]),
(4,[199],52,[0]),
(4,[249],0,[-1]),
(5,[0,10,20,30,45],0,[-1]),
(5,[1,11,21,31,46],0,[-1]),
(5,[2,54,104,154,204],0,[-1]),
(5,[3,13,23,33,48],0,[-1]),
(5,[4,14,24,34,49,50,51,52,53,60,61,62,63,70,71,72,73,80,81,82,83,95,96,97,98,100,101,102,103,110,111,112,113,120,121,122,123,130,131,132,133,145,146,147,148,150,151,152,153,160,161,162,163,170,171,172,173,180,181,182,183,190,191,192,193,195,196,197,198,200,201,202,203,210,211,212,213,220,221,222,223,230,231,232,233,240,241,242,243,245,246,247,248],0,[-1]),
(5,[5,6,7,8,9,15,16,17,18,19,25,26,27,28,29,35,36,37,38,39,40,41,42,43,44,55,56,57,58,59,65,66,67,68,69,75,76,77,78,79,85,86,87,88,89,90,91,92,93,94,105,106,107,108,109,115,116,117,118,119,125,126,127,128,129,135,136,137,138,139,140,141,142,143,144,155,156,157,158,159,165,166,167,168,169,175,176,177,178,179,185,186,187,188,189,194,205,206,207,208,209,215,216,217,218,219,225,226,227,228,229,235,236,237,238,239,244],0,[-1]),
(5,[12,64,114,164,214],0,[-1]),
(5,[22,32,47],0,[-1]),
(5,[74,99],0,[-1]),
(5,[84,134,184,234],0,[-1]),
(5,[124,174,224],0,[-1]),
(5,[149],0,[-1]),
(5,[199],2,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(5,[199],5,[0,1,2,3]),
(5,[199],7,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(5,[199],9,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(5,[199],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(5,[199],15,[0,1,2,3]),
(5,[199],17,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(5,[199],19,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(5,[199],22,[0,1,2,3,4,5,6,7,8,9]),
(5,[199],24,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(5,[199],27,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(5,[199],29,[0,1,2,3,4,5,6,7,8,9]),
(5,[199],32,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]),
(5,[199],34,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]),
(5,[199],35,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]),
(5,[199],36,[0,1,2,3,4,5,6,7]),
(5,[199],38,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(5,[199],39,[0,1,2,3]),
(5,[199],40,[0,1,2,3]),
(5,[199],42,[0,2,3]),
(5,[249],0,[-1]),
(6,[0,10,20,30,45],0,[-1]),
(6,[1,11,21,31,46],0,[-1]),
(6,[2,54,104,154,204],0,[-1]),
(6,[3,13,23,33,48],0,[-1]),
(6,[4,14,24,34,49,50,51,52,53,60,61,62,63,70,71,72,73,80,81,82,83,95,96,97,98,100,101,102,103,110,111,112,113,120,121,122,123,130,131,132,133,145,146,147,148,150,151,152,153,160,161,162,163,170,171,172,173,180,181,182,183,190,191,192,193,195,196,197,198,200,201,202,203,210,211,212,213,220,221,222,223,230,231,232,233,240,241,242,243,245,246,247,248],0,[-1]),
(6,[5,6,7,8,9,15,16,17,18,19,25,26,27,28,29,35,36,37,38,39,40,41,42,43,44,55,56,57,58,59,65,66,67,68,69,75,76,77,78,79,85,86,87,88,89,90,91,92,93,94,105,106,107,108,109,115,116,117,118,119,125,126,127,128,129,135,136,137,138,139,140,141,142,143,144,155,156,157,158,159,165,166,167,168,169,175,176,177,178,179,185,186,187,188,189,194,205,206,207,208,209,215,216,217,218,219,225,226,227,228,229,235,236,237,238,239,244],0,[-1]),
(6,[12,64,114,164,214],0,[-1]),
(6,[22,32,47],0,[-1]),
(6,[74,99],0,[-1]),
(6,[84,134,184,234],0,[-1]),
(6,[124,174,224],0,[-1]),
(6,[149],0,[-1]),
(6,[199],0,[-1]),
(6,[249],0,[-1])]
private def checkedTasks : List CoverageTask := [(0,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 16 false).zipIdx.map Prod.swap),(3, (List.replicate 16 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 4 false).zipIdx.map Prod.swap),(6, (List.replicate 25 true).zipIdx.map Prod.swap),(7, (List.replicate 16 false).zipIdx.map Prod.swap),(8, (List.replicate 16 true).zipIdx.map Prod.swap),(9, (List.replicate 16 true).zipIdx.map Prod.swap),(10, (List.replicate 16 false).zipIdx.map Prod.swap),(11, (List.replicate 10 true).zipIdx.map Prod.swap),(12, (List.replicate 16 false).zipIdx.map Prod.swap),(13, (List.replicate 4 true).zipIdx.map Prod.swap),(14, (List.replicate 4 true).zipIdx.map Prod.swap),(15, (List.replicate 4 false).zipIdx.map Prod.swap),(16, (List.replicate 10 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 10 true).zipIdx.map Prod.swap),(19, (List.replicate 25 false).zipIdx.map Prod.swap),(20, (List.replicate 2 true).zipIdx.map Prod.swap),(21, (List.replicate 8 true).zipIdx.map Prod.swap)]),(1,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 16 false).zipIdx.map Prod.swap),(3, (List.replicate 16 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 4 false).zipIdx.map Prod.swap),(6, (List.replicate 25 true).zipIdx.map Prod.swap),(7, (List.replicate 16 false).zipIdx.map Prod.swap),(8, (List.replicate 16 true).zipIdx.map Prod.swap),(9, (List.replicate 16 true).zipIdx.map Prod.swap),(10, (List.replicate 16 false).zipIdx.map Prod.swap),(11, (List.replicate 4 true).zipIdx.map Prod.swap),(12, (List.replicate 25 false).zipIdx.map Prod.swap),(13, (List.replicate 10 true).zipIdx.map Prod.swap),(14, (List.replicate 10 false).zipIdx.map Prod.swap),(15, (List.replicate 10 true).zipIdx.map Prod.swap),(16, (List.replicate 10 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 5 true).zipIdx.map Prod.swap),(19, (List.replicate 20 false).zipIdx.map Prod.swap),(20, (List.replicate 2 true).zipIdx.map Prod.swap),(21, [false, true, false, false].zipIdx.map Prod.swap)]),(2,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 16 false).zipIdx.map Prod.swap),(3, (List.replicate 16 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 4 false).zipIdx.map Prod.swap),(6, (List.replicate 25 true).zipIdx.map Prod.swap),(7, (List.replicate 16 false).zipIdx.map Prod.swap),(8, (List.replicate 16 true).zipIdx.map Prod.swap),(9, (List.replicate 16 true).zipIdx.map Prod.swap),(10, (List.replicate 16 false).zipIdx.map Prod.swap),(11, (List.replicate 4 true).zipIdx.map Prod.swap),(12, (List.replicate 25 false).zipIdx.map Prod.swap),(13, (List.replicate 10 true).zipIdx.map Prod.swap),(14, (List.replicate 10 false).zipIdx.map Prod.swap),(15, (List.replicate 10 true).zipIdx.map Prod.swap),(16, (List.replicate 4 true).zipIdx.map Prod.swap),(17, (List.replicate 10 true).zipIdx.map Prod.swap),(18, (List.replicate 10 false).zipIdx.map Prod.swap),(19, (List.replicate 10 true).zipIdx.map Prod.swap),(20, (List.replicate 10 false).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 10 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 10 true).zipIdx.map Prod.swap),(27, (List.replicate 25 false).zipIdx.map Prod.swap),(28, (List.replicate 5 true).zipIdx.map Prod.swap),(29, (List.replicate 20 false).zipIdx.map Prod.swap),(30, [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false].zipIdx.map Prod.swap),(31, (List.replicate 1 false).zipIdx.map Prod.swap),(32, (List.replicate 2 true).zipIdx.map Prod.swap),(33, (List.replicate 4 true).zipIdx.map Prod.swap)]),(3,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 16 false).zipIdx.map Prod.swap),(3, (List.replicate 16 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 4 false).zipIdx.map Prod.swap),(6, (List.replicate 16 true).zipIdx.map Prod.swap),(7, (List.replicate 25 false).zipIdx.map Prod.swap),(8, (List.replicate 25 true).zipIdx.map Prod.swap),(9, (List.replicate 25 false).zipIdx.map Prod.swap),(10, (List.replicate 25 true).zipIdx.map Prod.swap),(11, (List.replicate 4 true).zipIdx.map Prod.swap),(12, (List.replicate 25 false).zipIdx.map Prod.swap),(13, (List.replicate 10 true).zipIdx.map Prod.swap),(14, (List.replicate 10 false).zipIdx.map Prod.swap),(15, (List.replicate 10 true).zipIdx.map Prod.swap),(16, (List.replicate 16 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 25 true).zipIdx.map Prod.swap),(19, (List.replicate 25 false).zipIdx.map Prod.swap),(20, (List.replicate 25 true).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 25 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 4 true).zipIdx.map Prod.swap),(27, (List.replicate 25 false).zipIdx.map Prod.swap),(28, (List.replicate 10 true).zipIdx.map Prod.swap),(29, (List.replicate 10 false).zipIdx.map Prod.swap),(30, (List.replicate 10 true).zipIdx.map Prod.swap),(31, (List.replicate 8 true).zipIdx.map Prod.swap),(32, (List.replicate 20 false).zipIdx.map Prod.swap),(33, (List.replicate 4 true).zipIdx.map Prod.swap),(34, (List.replicate 16 false).zipIdx.map Prod.swap),(35, (List.replicate 16 false).zipIdx.map Prod.swap),(36, (List.replicate 4 false).zipIdx.map Prod.swap),(37, (List.replicate 4 true).zipIdx.map Prod.swap),(38, (List.replicate 16 false).zipIdx.map Prod.swap),(39, (List.replicate 4 false).zipIdx.map Prod.swap),(40, (List.replicate 4 false).zipIdx.map Prod.swap),(41, (List.replicate 2 true).zipIdx.map Prod.swap),(42, [false, true, false, false].zipIdx.map Prod.swap)]),(4,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 16 false).zipIdx.map Prod.swap),(3, (List.replicate 16 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 4 false).zipIdx.map Prod.swap),(6, (List.replicate 16 true).zipIdx.map Prod.swap),(7, (List.replicate 25 false).zipIdx.map Prod.swap),(8, (List.replicate 25 true).zipIdx.map Prod.swap),(9, (List.replicate 25 false).zipIdx.map Prod.swap),(10, (List.replicate 25 true).zipIdx.map Prod.swap),(11, (List.replicate 4 true).zipIdx.map Prod.swap),(12, (List.replicate 25 false).zipIdx.map Prod.swap),(13, (List.replicate 10 true).zipIdx.map Prod.swap),(14, (List.replicate 10 false).zipIdx.map Prod.swap),(15, (List.replicate 10 true).zipIdx.map Prod.swap),(16, (List.replicate 16 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 25 true).zipIdx.map Prod.swap),(19, (List.replicate 25 false).zipIdx.map Prod.swap),(20, (List.replicate 25 true).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 25 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 4 true).zipIdx.map Prod.swap),(27, (List.replicate 25 false).zipIdx.map Prod.swap),(28, (List.replicate 10 true).zipIdx.map Prod.swap),(29, (List.replicate 10 false).zipIdx.map Prod.swap),(30, (List.replicate 10 true).zipIdx.map Prod.swap),(31, (List.replicate 4 true).zipIdx.map Prod.swap),(32, (List.replicate 10 true).zipIdx.map Prod.swap),(33, (List.replicate 10 false).zipIdx.map Prod.swap),(34, (List.replicate 10 true).zipIdx.map Prod.swap),(35, (List.replicate 10 false).zipIdx.map Prod.swap),(36, (List.replicate 4 true).zipIdx.map Prod.swap),(37, (List.replicate 10 false).zipIdx.map Prod.swap),(38, (List.replicate 10 true).zipIdx.map Prod.swap),(39, (List.replicate 10 false).zipIdx.map Prod.swap),(40, (List.replicate 10 true).zipIdx.map Prod.swap),(41, (List.replicate 8 true).zipIdx.map Prod.swap),(42, (List.replicate 20 false).zipIdx.map Prod.swap),(43, (List.replicate 4 true).zipIdx.map Prod.swap),(44, (List.replicate 16 false).zipIdx.map Prod.swap),(45, (List.replicate 16 false).zipIdx.map Prod.swap),(46, (List.replicate 4 false).zipIdx.map Prod.swap),(47, (List.replicate 4 true).zipIdx.map Prod.swap),(48, (List.replicate 16 false).zipIdx.map Prod.swap),(49, (List.replicate 4 false).zipIdx.map Prod.swap),(50, (List.replicate 4 false).zipIdx.map Prod.swap),(51, [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false].zipIdx.map Prod.swap),(52, (List.replicate 1 false).zipIdx.map Prod.swap),(53, (List.replicate 2 true).zipIdx.map Prod.swap),(54, (List.replicate 4 true).zipIdx.map Prod.swap)]),(5,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 16 false).zipIdx.map Prod.swap),(3, (List.replicate 16 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 4 false).zipIdx.map Prod.swap),(6, (List.replicate 16 true).zipIdx.map Prod.swap),(7, (List.replicate 25 false).zipIdx.map Prod.swap),(8, (List.replicate 25 true).zipIdx.map Prod.swap),(9, (List.replicate 25 false).zipIdx.map Prod.swap),(10, (List.replicate 25 true).zipIdx.map Prod.swap),(11, (List.replicate 10 true).zipIdx.map Prod.swap),(12, (List.replicate 16 false).zipIdx.map Prod.swap),(13, (List.replicate 4 true).zipIdx.map Prod.swap),(14, (List.replicate 4 true).zipIdx.map Prod.swap),(15, (List.replicate 4 false).zipIdx.map Prod.swap),(16, (List.replicate 16 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 25 true).zipIdx.map Prod.swap),(19, (List.replicate 25 false).zipIdx.map Prod.swap),(20, (List.replicate 25 true).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 25 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 4 true).zipIdx.map Prod.swap),(27, (List.replicate 25 false).zipIdx.map Prod.swap),(28, (List.replicate 10 true).zipIdx.map Prod.swap),(29, (List.replicate 10 false).zipIdx.map Prod.swap),(30, (List.replicate 10 true).zipIdx.map Prod.swap),(31, (List.replicate 8 true).zipIdx.map Prod.swap),(32, (List.replicate 20 false).zipIdx.map Prod.swap),(33, (List.replicate 8 true).zipIdx.map Prod.swap),(34, (List.replicate 20 false).zipIdx.map Prod.swap),(35, (List.replicate 20 false).zipIdx.map Prod.swap),(36, (List.replicate 8 false).zipIdx.map Prod.swap),(37, (List.replicate 4 true).zipIdx.map Prod.swap),(38, (List.replicate 16 false).zipIdx.map Prod.swap),(39, (List.replicate 4 false).zipIdx.map Prod.swap),(40, (List.replicate 4 false).zipIdx.map Prod.swap),(41, (List.replicate 2 true).zipIdx.map Prod.swap),(42, [false, true, false, false].zipIdx.map Prod.swap)]),(6,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 16 false).zipIdx.map Prod.swap),(3, (List.replicate 16 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 4 false).zipIdx.map Prod.swap),(6, (List.replicate 16 true).zipIdx.map Prod.swap),(7, (List.replicate 25 false).zipIdx.map Prod.swap),(8, (List.replicate 25 true).zipIdx.map Prod.swap),(9, (List.replicate 25 false).zipIdx.map Prod.swap),(10, (List.replicate 25 true).zipIdx.map Prod.swap),(11, (List.replicate 10 true).zipIdx.map Prod.swap),(12, (List.replicate 16 false).zipIdx.map Prod.swap),(13, (List.replicate 4 true).zipIdx.map Prod.swap),(14, (List.replicate 4 true).zipIdx.map Prod.swap),(15, (List.replicate 4 false).zipIdx.map Prod.swap),(16, (List.replicate 16 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 25 true).zipIdx.map Prod.swap),(19, (List.replicate 25 false).zipIdx.map Prod.swap),(20, (List.replicate 25 true).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 25 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 4 true).zipIdx.map Prod.swap),(27, (List.replicate 25 false).zipIdx.map Prod.swap),(28, (List.replicate 10 true).zipIdx.map Prod.swap),(29, (List.replicate 10 false).zipIdx.map Prod.swap),(30, (List.replicate 10 true).zipIdx.map Prod.swap),(31, (List.replicate 4 true).zipIdx.map Prod.swap),(32, (List.replicate 10 true).zipIdx.map Prod.swap),(33, (List.replicate 10 false).zipIdx.map Prod.swap),(34, (List.replicate 10 true).zipIdx.map Prod.swap),(35, (List.replicate 10 false).zipIdx.map Prod.swap),(36, (List.replicate 4 true).zipIdx.map Prod.swap),(37, (List.replicate 10 false).zipIdx.map Prod.swap),(38, (List.replicate 10 true).zipIdx.map Prod.swap),(39, (List.replicate 10 false).zipIdx.map Prod.swap),(40, (List.replicate 10 true).zipIdx.map Prod.swap),(41, (List.replicate 8 true).zipIdx.map Prod.swap),(42, (List.replicate 20 false).zipIdx.map Prod.swap),(43, (List.replicate 8 true).zipIdx.map Prod.swap),(44, (List.replicate 20 false).zipIdx.map Prod.swap),(45, (List.replicate 20 false).zipIdx.map Prod.swap),(46, (List.replicate 8 false).zipIdx.map Prod.swap),(47, (List.replicate 4 true).zipIdx.map Prod.swap),(48, (List.replicate 16 false).zipIdx.map Prod.swap),(49, (List.replicate 4 false).zipIdx.map Prod.swap),(50, (List.replicate 4 false).zipIdx.map Prod.swap),(51, [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false].zipIdx.map Prod.swap),(52, (List.replicate 1 false).zipIdx.map Prod.swap),(53, (List.replicate 2 true).zipIdx.map Prod.swap),(54, (List.replicate 4 true).zipIdx.map Prod.swap)])]
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
private abbrev specAt8 (pi goal : ℕ) : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) pi))[goal-1]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private abbrev cSpec8_0_1 := specAt8 0 1
private theorem cFlags8_0_1 : automaticFlags (trunkCatalog.states 8).context cSpec8_0_1 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_2 coordinateInput8_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_2 hCoordinate8_1]
  decide +kernel
private abbrev cSpec8_0_2 := specAt8 0 2
private theorem cFlags8_0_2 : automaticFlags (trunkCatalog.states 8).context cSpec8_0_2 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_4 coordinateInput8_5 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_4 hCoordinate8_5]
  decide +kernel
private abbrev cSpec8_0_3 := specAt8 0 3
private theorem cFlags8_0_3 : automaticFlags (trunkCatalog.states 8).context cSpec8_0_3 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_6 coordinateInput8_7 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_6 hCoordinate8_7]
  decide +kernel
private abbrev cSpec8_0_4 := specAt8 0 4
private theorem cFlags8_0_4 : automaticFlags (trunkCatalog.states 8).context cSpec8_0_4 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_8 coordinateInput8_9 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_8 hCoordinate8_9]
  decide +kernel
private abbrev cSpec8_0_5 := specAt8 0 5
private theorem cFlags8_0_5 : automaticFlags (trunkCatalog.states 8).context cSpec8_0_5 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_10 coordinateInput8_11 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_10 hCoordinate8_11]
  decide +kernel
private abbrev cSpec8_0_6 := specAt8 0 6
private theorem cFlags8_0_6 : automaticFlags (trunkCatalog.states 8).context cSpec8_0_6 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_0 coordinateInput8_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_0 hCoordinate8_3]
  decide +kernel
private abbrev cSpec8_0_7 := specAt8 0 7
private theorem cFlags8_0_7 : automaticFlags (trunkCatalog.states 8).context cSpec8_0_7 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_12 coordinateInput8_13 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_12 hCoordinate8_13]
  decide +kernel
private abbrev cSpec8_0_8 := specAt8 0 8
private theorem cFlags8_0_8 : automaticFlags (trunkCatalog.states 8).context cSpec8_0_8 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_14 coordinateInput8_15 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_14 hCoordinate8_15]
  decide +kernel
private abbrev cSpec8_0_9 := specAt8 0 9
private theorem cFlags8_0_9 : automaticFlags (trunkCatalog.states 8).context cSpec8_0_9 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_16 coordinateInput8_17 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_16 hCoordinate8_17]
  decide +kernel
private abbrev cSpec8_0_10 := specAt8 0 10
private theorem cFlags8_0_10 : automaticFlags (trunkCatalog.states 8).context cSpec8_0_10 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_18 coordinateInput8_19 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_18 hCoordinate8_19]
  decide +kernel
private abbrev cSpec8_0_11 := specAt8 0 11
private theorem cFlags8_0_11 : automaticFlags (trunkCatalog.states 8).context cSpec8_0_11 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_20 coordinateInput8_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_20 hCoordinate8_21]
  decide +kernel
private abbrev cSpec8_0_12 := specAt8 0 12
private theorem cFlags8_0_12 : automaticFlags (trunkCatalog.states 8).context cSpec8_0_12 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_22 coordinateInput8_23 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_22 hCoordinate8_23]
  decide +kernel
private abbrev cSpec8_0_13 := specAt8 0 13
private theorem cFlags8_0_13 : automaticFlags (trunkCatalog.states 8).context cSpec8_0_13 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_24 coordinateInput8_25 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_24 hCoordinate8_25]
  decide +kernel
private abbrev cSpec8_0_14 := specAt8 0 14
private theorem cFlags8_0_14 : automaticFlags (trunkCatalog.states 8).context cSpec8_0_14 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_26 coordinateInput8_27 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_26 hCoordinate8_27]
  decide +kernel
private abbrev cSpec8_0_15 := specAt8 0 15
private theorem cFlags8_0_15 : automaticFlags (trunkCatalog.states 8).context cSpec8_0_15 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_28 coordinateInput8_29 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_28 hCoordinate8_29]
  decide +kernel
private abbrev cSpec8_0_16 := specAt8 0 16
private theorem cFlags8_0_16 : automaticFlags (trunkCatalog.states 8).context cSpec8_0_16 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_2 coordinateInput8_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_2 hCoordinate8_3]
  decide +kernel
private abbrev cSpec8_0_17 := specAt8 0 17
private theorem cFlags8_0_17 : automaticFlags (trunkCatalog.states 8).context cSpec8_0_17 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_0 coordinateInput8_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_0 hCoordinate8_1]
  decide +kernel
private abbrev cSpec8_0_18 := specAt8 0 18
private theorem cFlags8_0_18 : automaticFlags (trunkCatalog.states 8).context cSpec8_0_18 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_0 coordinateInput8_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_0 hCoordinate8_21]
  decide +kernel
private abbrev cSpec8_0_19 := specAt8 0 19
private theorem cFlags8_0_19 : automaticFlags (trunkCatalog.states 8).context cSpec8_0_19 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_20 coordinateInput8_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_20 hCoordinate8_3]
  decide +kernel
private abbrev cSpec8_0_20 := specAt8 0 20
private theorem cFlags8_0_20 : automaticFlags (trunkCatalog.states 8).context cSpec8_0_20 = (List.replicate 2 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_2 coordinateInput8_30 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_2 hCoordinate8_30]
  decide +kernel
private abbrev cSpec8_0_21 := specAt8 0 21
private theorem cFlags8_0_21 : automaticFlags (trunkCatalog.states 8).context cSpec8_0_21 = (List.replicate 8 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_31 coordinateInput8_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_31 hCoordinate8_21]
  decide +kernel
private abbrev cSpec8_1_1 := specAt8 1 1
private theorem cFlags8_1_1 : automaticFlags (trunkCatalog.states 8).context cSpec8_1_1 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_1

private abbrev cSpec8_1_2 := specAt8 1 2
private theorem cFlags8_1_2 : automaticFlags (trunkCatalog.states 8).context cSpec8_1_2 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec8_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_2

private abbrev cSpec8_1_3 := specAt8 1 3
private theorem cFlags8_1_3 : automaticFlags (trunkCatalog.states 8).context cSpec8_1_3 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_3

private abbrev cSpec8_1_4 := specAt8 1 4
private theorem cFlags8_1_4 : automaticFlags (trunkCatalog.states 8).context cSpec8_1_4 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_4

private abbrev cSpec8_1_5 := specAt8 1 5
private theorem cFlags8_1_5 : automaticFlags (trunkCatalog.states 8).context cSpec8_1_5 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec8_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_5

private abbrev cSpec8_1_6 := specAt8 1 6
private theorem cFlags8_1_6 : automaticFlags (trunkCatalog.states 8).context cSpec8_1_6 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_6

private abbrev cSpec8_1_7 := specAt8 1 7
private theorem cFlags8_1_7 : automaticFlags (trunkCatalog.states 8).context cSpec8_1_7 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec8_0_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_7

private abbrev cSpec8_1_8 := specAt8 1 8
private theorem cFlags8_1_8 : automaticFlags (trunkCatalog.states 8).context cSpec8_1_8 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_8

private abbrev cSpec8_1_9 := specAt8 1 9
private theorem cFlags8_1_9 : automaticFlags (trunkCatalog.states 8).context cSpec8_1_9 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_9

private abbrev cSpec8_1_10 := specAt8 1 10
private theorem cFlags8_1_10 : automaticFlags (trunkCatalog.states 8).context cSpec8_1_10 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec8_0_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_10

private abbrev cSpec8_1_11 := specAt8 1 11
private theorem cFlags8_1_11 : automaticFlags (trunkCatalog.states 8).context cSpec8_1_11 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_32 coordinateInput8_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_32 hCoordinate8_33]
  decide +kernel
private abbrev cSpec8_1_12 := specAt8 1 12
private theorem cFlags8_1_12 : automaticFlags (trunkCatalog.states 8).context cSpec8_1_12 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_34 coordinateInput8_35 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_34 hCoordinate8_35]
  decide +kernel
private abbrev cSpec8_1_13 := specAt8 1 13
private theorem cFlags8_1_13 : automaticFlags (trunkCatalog.states 8).context cSpec8_1_13 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_36 coordinateInput8_37 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_36 hCoordinate8_37]
  decide +kernel
private abbrev cSpec8_1_14 := specAt8 1 14
private theorem cFlags8_1_14 : automaticFlags (trunkCatalog.states 8).context cSpec8_1_14 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_38 coordinateInput8_39 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_38 hCoordinate8_39]
  decide +kernel
private abbrev cSpec8_1_15 := specAt8 1 15
private theorem cFlags8_1_15 : automaticFlags (trunkCatalog.states 8).context cSpec8_1_15 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_40 coordinateInput8_41 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_40 hCoordinate8_41]
  decide +kernel
private abbrev cSpec8_1_16 := specAt8 1 16
private theorem cFlags8_1_16 : automaticFlags (trunkCatalog.states 8).context cSpec8_1_16 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_16

private abbrev cSpec8_1_17 := specAt8 1 17
private theorem cFlags8_1_17 : automaticFlags (trunkCatalog.states 8).context cSpec8_1_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_0_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_17

private abbrev cSpec8_1_18 := specAt8 1 18
private theorem cFlags8_1_18 : automaticFlags (trunkCatalog.states 8).context cSpec8_1_18 = (List.replicate 5 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_0 coordinateInput8_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_0 hCoordinate8_33]
  decide +kernel
private abbrev cSpec8_1_19 := specAt8 1 19
private theorem cFlags8_1_19 : automaticFlags (trunkCatalog.states 8).context cSpec8_1_19 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_32 coordinateInput8_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_32 hCoordinate8_3]
  decide +kernel
private abbrev cSpec8_1_20 := specAt8 1 20
private theorem cFlags8_1_20 : automaticFlags (trunkCatalog.states 8).context cSpec8_1_20 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_20

private abbrev cSpec8_1_21 := specAt8 1 21
private theorem cFlags8_1_21 : automaticFlags (trunkCatalog.states 8).context cSpec8_1_21 = [false, true, false, false] := by
  rw [automaticFlags_cached _ _ coordinateInput8_31 coordinateInput8_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_31 hCoordinate8_33]
  decide +kernel
private abbrev cSpec8_2_1 := specAt8 2 1
private theorem cFlags8_2_1 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_1 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_1

private abbrev cSpec8_2_2 := specAt8 2 2
private theorem cFlags8_2_2 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_2 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec8_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_2

private abbrev cSpec8_2_3 := specAt8 2 3
private theorem cFlags8_2_3 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_3 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_3

private abbrev cSpec8_2_4 := specAt8 2 4
private theorem cFlags8_2_4 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_4 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_4

private abbrev cSpec8_2_5 := specAt8 2 5
private theorem cFlags8_2_5 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_5 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec8_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_5

private abbrev cSpec8_2_6 := specAt8 2 6
private theorem cFlags8_2_6 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_6 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_6

private abbrev cSpec8_2_7 := specAt8 2 7
private theorem cFlags8_2_7 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_7 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec8_0_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_7

private abbrev cSpec8_2_8 := specAt8 2 8
private theorem cFlags8_2_8 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_8 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_8

private abbrev cSpec8_2_9 := specAt8 2 9
private theorem cFlags8_2_9 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_9 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_9

private abbrev cSpec8_2_10 := specAt8 2 10
private theorem cFlags8_2_10 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_10 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec8_0_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_10

private abbrev cSpec8_2_11 := specAt8 2 11
private theorem cFlags8_2_11 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_11 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_11

private abbrev cSpec8_2_12 := specAt8 2 12
private theorem cFlags8_2_12 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_12 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_12

private abbrev cSpec8_2_13 := specAt8 2 13
private theorem cFlags8_2_13 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_13 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_13

private abbrev cSpec8_2_14 := specAt8 2 14
private theorem cFlags8_2_14 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_14 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec8_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_14

private abbrev cSpec8_2_15 := specAt8 2 15
private theorem cFlags8_2_15 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_15 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_15

private abbrev cSpec8_2_16 := specAt8 2 16
private theorem cFlags8_2_16 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_16 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_42 coordinateInput8_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_42 hCoordinate8_43]
  decide +kernel
private abbrev cSpec8_2_17 := specAt8 2 17
private theorem cFlags8_2_17 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_17 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_44 coordinateInput8_45 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_44 hCoordinate8_45]
  decide +kernel
private abbrev cSpec8_2_18 := specAt8 2 18
private theorem cFlags8_2_18 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_18 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_46 coordinateInput8_47 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_46 hCoordinate8_47]
  decide +kernel
private abbrev cSpec8_2_19 := specAt8 2 19
private theorem cFlags8_2_19 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_19 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_48 coordinateInput8_49 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_48 hCoordinate8_49]
  decide +kernel
private abbrev cSpec8_2_20 := specAt8 2 20
private theorem cFlags8_2_20 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_20 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_50 coordinateInput8_51 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_50 hCoordinate8_51]
  decide +kernel
private abbrev cSpec8_2_21 := specAt8 2 21
private theorem cFlags8_2_21 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_21 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_52 coordinateInput8_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_52 hCoordinate8_53]
  decide +kernel
private abbrev cSpec8_2_22 := specAt8 2 22
private theorem cFlags8_2_22 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_22 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_54 coordinateInput8_55 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_54 hCoordinate8_55]
  decide +kernel
private abbrev cSpec8_2_23 := specAt8 2 23
private theorem cFlags8_2_23 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_23 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_56 coordinateInput8_57 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_56 hCoordinate8_57]
  decide +kernel
private abbrev cSpec8_2_24 := specAt8 2 24
private theorem cFlags8_2_24 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_24 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_58 coordinateInput8_59 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_58 hCoordinate8_59]
  decide +kernel
private abbrev cSpec8_2_25 := specAt8 2 25
private theorem cFlags8_2_25 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_25 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_60 coordinateInput8_61 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_60 hCoordinate8_61]
  decide +kernel
private abbrev cSpec8_2_26 := specAt8 2 26
private theorem cFlags8_2_26 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_26 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_16

private abbrev cSpec8_2_27 := specAt8 2 27
private theorem cFlags8_2_27 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_0_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_17

private abbrev cSpec8_2_28 := specAt8 2 28
private theorem cFlags8_2_28 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_28 = (List.replicate 5 true) := by
  exact (automaticFlags_same _ _ cSpec8_1_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_18

private abbrev cSpec8_2_29 := specAt8 2 29
private theorem cFlags8_2_29 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_29 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec8_1_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_19

private abbrev cSpec8_2_30 := specAt8 2 30
private theorem cFlags8_2_30 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_30 = [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false] := by
  rw [automaticFlags_cached _ _ coordinateInput8_32 coordinateInput8_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_32 hCoordinate8_43]
  decide +kernel
private abbrev cSpec8_2_31 := specAt8 2 31
private theorem cFlags8_2_31 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_31 = (List.replicate 1 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_42 coordinateInput8_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_42 hCoordinate8_33]
  decide +kernel
private abbrev cSpec8_2_32 := specAt8 2 32
private theorem cFlags8_2_32 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_32 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_20

private abbrev cSpec8_2_33 := specAt8 2 33
private theorem cFlags8_2_33 : automaticFlags (trunkCatalog.states 8).context cSpec8_2_33 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_31 coordinateInput8_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_31 hCoordinate8_53]
  decide +kernel
private abbrev cSpec8_3_1 := specAt8 3 1
private theorem cFlags8_3_1 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_1 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_1

private abbrev cSpec8_3_2 := specAt8 3 2
private theorem cFlags8_3_2 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_2 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec8_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_2

private abbrev cSpec8_3_3 := specAt8 3 3
private theorem cFlags8_3_3 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_3 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_3

private abbrev cSpec8_3_4 := specAt8 3 4
private theorem cFlags8_3_4 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_4 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_4

private abbrev cSpec8_3_5 := specAt8 3 5
private theorem cFlags8_3_5 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_5 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec8_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_5

private abbrev cSpec8_3_6 := specAt8 3 6
private theorem cFlags8_3_6 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_6 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_62 coordinateInput8_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_62 hCoordinate8_63]
  decide +kernel
private abbrev cSpec8_3_7 := specAt8 3 7
private theorem cFlags8_3_7 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_7 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_64 coordinateInput8_65 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_64 hCoordinate8_65]
  decide +kernel
private abbrev cSpec8_3_8 := specAt8 3 8
private theorem cFlags8_3_8 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_8 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_66 coordinateInput8_67 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_66 hCoordinate8_67]
  decide +kernel
private abbrev cSpec8_3_9 := specAt8 3 9
private theorem cFlags8_3_9 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_9 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_68 coordinateInput8_69 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_68 hCoordinate8_69]
  decide +kernel
private abbrev cSpec8_3_10 := specAt8 3 10
private theorem cFlags8_3_10 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_10 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_70 coordinateInput8_71 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_70 hCoordinate8_71]
  decide +kernel
private abbrev cSpec8_3_11 := specAt8 3 11
private theorem cFlags8_3_11 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_11 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_72 coordinateInput8_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_72 hCoordinate8_73]
  decide +kernel
private abbrev cSpec8_3_12 := specAt8 3 12
private theorem cFlags8_3_12 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_12 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_74 coordinateInput8_75 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_74 hCoordinate8_75]
  decide +kernel
private abbrev cSpec8_3_13 := specAt8 3 13
private theorem cFlags8_3_13 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_13 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_76 coordinateInput8_77 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_76 hCoordinate8_77]
  decide +kernel
private abbrev cSpec8_3_14 := specAt8 3 14
private theorem cFlags8_3_14 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_14 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_78 coordinateInput8_79 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_78 hCoordinate8_79]
  decide +kernel
private abbrev cSpec8_3_15 := specAt8 3 15
private theorem cFlags8_3_15 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_15 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_80 coordinateInput8_81 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_80 hCoordinate8_81]
  decide +kernel
private abbrev cSpec8_3_16 := specAt8 3 16
private theorem cFlags8_3_16 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_16 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_82 coordinateInput8_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_82 hCoordinate8_83]
  decide +kernel
private abbrev cSpec8_3_17 := specAt8 3 17
private theorem cFlags8_3_17 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_17 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_84 coordinateInput8_85 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_84 hCoordinate8_85]
  decide +kernel
private abbrev cSpec8_3_18 := specAt8 3 18
private theorem cFlags8_3_18 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_18 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_86 coordinateInput8_87 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_86 hCoordinate8_87]
  decide +kernel
private abbrev cSpec8_3_19 := specAt8 3 19
private theorem cFlags8_3_19 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_19 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_88 coordinateInput8_89 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_88 hCoordinate8_89]
  decide +kernel
private abbrev cSpec8_3_20 := specAt8 3 20
private theorem cFlags8_3_20 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_20 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_90 coordinateInput8_91 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_90 hCoordinate8_91]
  decide +kernel
private abbrev cSpec8_3_21 := specAt8 3 21
private theorem cFlags8_3_21 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_21 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_92 coordinateInput8_93 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_92 hCoordinate8_93]
  decide +kernel
private abbrev cSpec8_3_22 := specAt8 3 22
private theorem cFlags8_3_22 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_22 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_94 coordinateInput8_95 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_94 hCoordinate8_95]
  decide +kernel
private abbrev cSpec8_3_23 := specAt8 3 23
private theorem cFlags8_3_23 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_23 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_96 coordinateInput8_97 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_96 hCoordinate8_97]
  decide +kernel
private abbrev cSpec8_3_24 := specAt8 3 24
private theorem cFlags8_3_24 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_24 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_98 coordinateInput8_99 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_98 hCoordinate8_99]
  decide +kernel
private abbrev cSpec8_3_25 := specAt8 3 25
private theorem cFlags8_3_25 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_25 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_100 coordinateInput8_101 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_100 hCoordinate8_101]
  decide +kernel
private abbrev cSpec8_3_26 := specAt8 3 26
private theorem cFlags8_3_26 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_11

private abbrev cSpec8_3_27 := specAt8 3 27
private theorem cFlags8_3_27 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_12

private abbrev cSpec8_3_28 := specAt8 3 28
private theorem cFlags8_3_28 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_13

private abbrev cSpec8_3_29 := specAt8 3 29
private theorem cFlags8_3_29 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec8_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_14

private abbrev cSpec8_3_30 := specAt8 3 30
private theorem cFlags8_3_30 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_15

private abbrev cSpec8_3_31 := specAt8 3 31
private theorem cFlags8_3_31 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_31 = (List.replicate 8 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_2 coordinateInput8_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_2 hCoordinate8_63]
  decide +kernel
private abbrev cSpec8_3_32 := specAt8 3 32
private theorem cFlags8_3_32 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_32 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_62 coordinateInput8_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_62 hCoordinate8_1]
  decide +kernel
private abbrev cSpec8_3_33 := specAt8 3 33
private theorem cFlags8_3_33 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_33 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_62 coordinateInput8_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_62 hCoordinate8_73]
  decide +kernel
private abbrev cSpec8_3_34 := specAt8 3 34
private theorem cFlags8_3_34 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_34 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_72 coordinateInput8_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_72 hCoordinate8_63]
  decide +kernel
private abbrev cSpec8_3_35 := specAt8 3 35
private theorem cFlags8_3_35 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_35 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_72 coordinateInput8_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_72 hCoordinate8_83]
  decide +kernel
private abbrev cSpec8_3_36 := specAt8 3 36
private theorem cFlags8_3_36 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_36 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_82 coordinateInput8_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_82 hCoordinate8_73]
  decide +kernel
private abbrev cSpec8_3_37 := specAt8 3 37
private theorem cFlags8_3_37 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_37 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_82 coordinateInput8_93 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_82 hCoordinate8_93]
  decide +kernel
private abbrev cSpec8_3_38 := specAt8 3 38
private theorem cFlags8_3_38 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_38 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_92 coordinateInput8_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_92 hCoordinate8_83]
  decide +kernel
private abbrev cSpec8_3_39 := specAt8 3 39
private theorem cFlags8_3_39 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_39 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_92 coordinateInput8_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_92 hCoordinate8_33]
  decide +kernel
private abbrev cSpec8_3_40 := specAt8 3 40
private theorem cFlags8_3_40 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_40 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_32 coordinateInput8_93 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_32 hCoordinate8_93]
  decide +kernel
private abbrev cSpec8_3_41 := specAt8 3 41
private theorem cFlags8_3_41 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_41 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_20

private abbrev cSpec8_3_42 := specAt8 3 42
private theorem cFlags8_3_42 : automaticFlags (trunkCatalog.states 8).context cSpec8_3_42 = [false, true, false, false] := by
  exact (automaticFlags_same _ _ cSpec8_1_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_21

private abbrev cSpec8_4_1 := specAt8 4 1
private theorem cFlags8_4_1 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_1 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_1

private abbrev cSpec8_4_2 := specAt8 4 2
private theorem cFlags8_4_2 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_2 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec8_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_2

private abbrev cSpec8_4_3 := specAt8 4 3
private theorem cFlags8_4_3 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_3 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_3

private abbrev cSpec8_4_4 := specAt8 4 4
private theorem cFlags8_4_4 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_4 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_4

private abbrev cSpec8_4_5 := specAt8 4 5
private theorem cFlags8_4_5 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_5 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec8_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_5

private abbrev cSpec8_4_6 := specAt8 4 6
private theorem cFlags8_4_6 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_6 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_6

private abbrev cSpec8_4_7 := specAt8 4 7
private theorem cFlags8_4_7 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_7 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_7

private abbrev cSpec8_4_8 := specAt8 4 8
private theorem cFlags8_4_8 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_8 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_8

private abbrev cSpec8_4_9 := specAt8 4 9
private theorem cFlags8_4_9 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_9 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_9

private abbrev cSpec8_4_10 := specAt8 4 10
private theorem cFlags8_4_10 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_10 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_10

private abbrev cSpec8_4_11 := specAt8 4 11
private theorem cFlags8_4_11 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_11 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_11

private abbrev cSpec8_4_12 := specAt8 4 12
private theorem cFlags8_4_12 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_12 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_12

private abbrev cSpec8_4_13 := specAt8 4 13
private theorem cFlags8_4_13 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_13 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_13

private abbrev cSpec8_4_14 := specAt8 4 14
private theorem cFlags8_4_14 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_14 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_14

private abbrev cSpec8_4_15 := specAt8 4 15
private theorem cFlags8_4_15 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_15 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_15

private abbrev cSpec8_4_16 := specAt8 4 16
private theorem cFlags8_4_16 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_16 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_16

private abbrev cSpec8_4_17 := specAt8 4 17
private theorem cFlags8_4_17 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_17

private abbrev cSpec8_4_18 := specAt8 4 18
private theorem cFlags8_4_18 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_18 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_18

private abbrev cSpec8_4_19 := specAt8 4 19
private theorem cFlags8_4_19 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_19 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_19

private abbrev cSpec8_4_20 := specAt8 4 20
private theorem cFlags8_4_20 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_20 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_20

private abbrev cSpec8_4_21 := specAt8 4 21
private theorem cFlags8_4_21 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_21 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_21

private abbrev cSpec8_4_22 := specAt8 4 22
private theorem cFlags8_4_22 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_22 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_22

private abbrev cSpec8_4_23 := specAt8 4 23
private theorem cFlags8_4_23 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_23 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_23

private abbrev cSpec8_4_24 := specAt8 4 24
private theorem cFlags8_4_24 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_24 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_24

private abbrev cSpec8_4_25 := specAt8 4 25
private theorem cFlags8_4_25 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_25 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_25

private abbrev cSpec8_4_26 := specAt8 4 26
private theorem cFlags8_4_26 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_11

private abbrev cSpec8_4_27 := specAt8 4 27
private theorem cFlags8_4_27 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_12

private abbrev cSpec8_4_28 := specAt8 4 28
private theorem cFlags8_4_28 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_13

private abbrev cSpec8_4_29 := specAt8 4 29
private theorem cFlags8_4_29 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec8_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_14

private abbrev cSpec8_4_30 := specAt8 4 30
private theorem cFlags8_4_30 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_15

private abbrev cSpec8_4_31 := specAt8 4 31
private theorem cFlags8_4_31 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_31 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_2_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_16

private abbrev cSpec8_4_32 := specAt8 4 32
private theorem cFlags8_4_32 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_32 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_2_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_17

private abbrev cSpec8_4_33 := specAt8 4 33
private theorem cFlags8_4_33 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_33 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec8_2_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_18

private abbrev cSpec8_4_34 := specAt8 4 34
private theorem cFlags8_4_34 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_34 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_2_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_19

private abbrev cSpec8_4_35 := specAt8 4 35
private theorem cFlags8_4_35 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_35 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec8_2_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_20

private abbrev cSpec8_4_36 := specAt8 4 36
private theorem cFlags8_4_36 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_36 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_2_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_21

private abbrev cSpec8_4_37 := specAt8 4 37
private theorem cFlags8_4_37 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_37 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec8_2_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_22

private abbrev cSpec8_4_38 := specAt8 4 38
private theorem cFlags8_4_38 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_38 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_2_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_23

private abbrev cSpec8_4_39 := specAt8 4 39
private theorem cFlags8_4_39 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_39 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec8_2_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_24

private abbrev cSpec8_4_40 := specAt8 4 40
private theorem cFlags8_4_40 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_40 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_2_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_25

private abbrev cSpec8_4_41 := specAt8 4 41
private theorem cFlags8_4_41 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_41 = (List.replicate 8 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_31

private abbrev cSpec8_4_42 := specAt8 4 42
private theorem cFlags8_4_42 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_42 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_32

private abbrev cSpec8_4_43 := specAt8 4 43
private theorem cFlags8_4_43 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_43 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_33 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_33

private abbrev cSpec8_4_44 := specAt8 4 44
private theorem cFlags8_4_44 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_44 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_34 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_34

private abbrev cSpec8_4_45 := specAt8 4 45
private theorem cFlags8_4_45 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_45 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_35 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_35

private abbrev cSpec8_4_46 := specAt8 4 46
private theorem cFlags8_4_46 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_46 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_36 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_36

private abbrev cSpec8_4_47 := specAt8 4 47
private theorem cFlags8_4_47 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_47 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_37 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_37

private abbrev cSpec8_4_48 := specAt8 4 48
private theorem cFlags8_4_48 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_48 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_38 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_38

private abbrev cSpec8_4_49 := specAt8 4 49
private theorem cFlags8_4_49 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_49 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_39 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_39

private abbrev cSpec8_4_50 := specAt8 4 50
private theorem cFlags8_4_50 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_50 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_40 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_40

private abbrev cSpec8_4_51 := specAt8 4 51
private theorem cFlags8_4_51 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_51 = [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false] := by
  exact (automaticFlags_same _ _ cSpec8_2_30 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_30

private abbrev cSpec8_4_52 := specAt8 4 52
private theorem cFlags8_4_52 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_52 = (List.replicate 1 false) := by
  exact (automaticFlags_same _ _ cSpec8_2_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_31

private abbrev cSpec8_4_53 := specAt8 4 53
private theorem cFlags8_4_53 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_53 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_20

private abbrev cSpec8_4_54 := specAt8 4 54
private theorem cFlags8_4_54 : automaticFlags (trunkCatalog.states 8).context cSpec8_4_54 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_2_33 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_33

private abbrev cSpec8_5_1 := specAt8 5 1
private theorem cFlags8_5_1 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_1 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_1

private abbrev cSpec8_5_2 := specAt8 5 2
private theorem cFlags8_5_2 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_2 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec8_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_2

private abbrev cSpec8_5_3 := specAt8 5 3
private theorem cFlags8_5_3 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_3 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_3

private abbrev cSpec8_5_4 := specAt8 5 4
private theorem cFlags8_5_4 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_4 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_4

private abbrev cSpec8_5_5 := specAt8 5 5
private theorem cFlags8_5_5 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_5 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec8_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_5

private abbrev cSpec8_5_6 := specAt8 5 6
private theorem cFlags8_5_6 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_6 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_6

private abbrev cSpec8_5_7 := specAt8 5 7
private theorem cFlags8_5_7 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_7 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_7

private abbrev cSpec8_5_8 := specAt8 5 8
private theorem cFlags8_5_8 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_8 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_8

private abbrev cSpec8_5_9 := specAt8 5 9
private theorem cFlags8_5_9 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_9 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_9

private abbrev cSpec8_5_10 := specAt8 5 10
private theorem cFlags8_5_10 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_10 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_10

private abbrev cSpec8_5_11 := specAt8 5 11
private theorem cFlags8_5_11 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_11 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_102 coordinateInput8_103 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_102 hCoordinate8_103]
  decide +kernel
private abbrev cSpec8_5_12 := specAt8 5 12
private theorem cFlags8_5_12 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_12 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_104 coordinateInput8_105 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_104 hCoordinate8_105]
  decide +kernel
private abbrev cSpec8_5_13 := specAt8 5 13
private theorem cFlags8_5_13 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_13 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_106 coordinateInput8_107 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_106 hCoordinate8_107]
  decide +kernel
private abbrev cSpec8_5_14 := specAt8 5 14
private theorem cFlags8_5_14 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_14 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_108 coordinateInput8_109 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_108 hCoordinate8_109]
  decide +kernel
private abbrev cSpec8_5_15 := specAt8 5 15
private theorem cFlags8_5_15 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_15 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_110 coordinateInput8_111 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_110 hCoordinate8_111]
  decide +kernel
private abbrev cSpec8_5_16 := specAt8 5 16
private theorem cFlags8_5_16 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_16 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_16

private abbrev cSpec8_5_17 := specAt8 5 17
private theorem cFlags8_5_17 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_17

private abbrev cSpec8_5_18 := specAt8 5 18
private theorem cFlags8_5_18 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_18 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_18

private abbrev cSpec8_5_19 := specAt8 5 19
private theorem cFlags8_5_19 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_19 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_19

private abbrev cSpec8_5_20 := specAt8 5 20
private theorem cFlags8_5_20 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_20 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_20

private abbrev cSpec8_5_21 := specAt8 5 21
private theorem cFlags8_5_21 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_21 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_21

private abbrev cSpec8_5_22 := specAt8 5 22
private theorem cFlags8_5_22 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_22 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_22

private abbrev cSpec8_5_23 := specAt8 5 23
private theorem cFlags8_5_23 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_23 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_23

private abbrev cSpec8_5_24 := specAt8 5 24
private theorem cFlags8_5_24 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_24 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_24

private abbrev cSpec8_5_25 := specAt8 5 25
private theorem cFlags8_5_25 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_25 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_25

private abbrev cSpec8_5_26 := specAt8 5 26
private theorem cFlags8_5_26 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_11

private abbrev cSpec8_5_27 := specAt8 5 27
private theorem cFlags8_5_27 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_12

private abbrev cSpec8_5_28 := specAt8 5 28
private theorem cFlags8_5_28 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_13

private abbrev cSpec8_5_29 := specAt8 5 29
private theorem cFlags8_5_29 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec8_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_14

private abbrev cSpec8_5_30 := specAt8 5 30
private theorem cFlags8_5_30 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_15

private abbrev cSpec8_5_31 := specAt8 5 31
private theorem cFlags8_5_31 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_31 = (List.replicate 8 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_31

private abbrev cSpec8_5_32 := specAt8 5 32
private theorem cFlags8_5_32 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_32 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_32

private abbrev cSpec8_5_33 := specAt8 5 33
private theorem cFlags8_5_33 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_33 = (List.replicate 8 true) := by
  rw [automaticFlags_cached _ _ coordinateInput8_62 coordinateInput8_103 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_62 hCoordinate8_103]
  decide +kernel
private abbrev cSpec8_5_34 := specAt8 5 34
private theorem cFlags8_5_34 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_34 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_102 coordinateInput8_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_102 hCoordinate8_63]
  decide +kernel
private abbrev cSpec8_5_35 := specAt8 5 35
private theorem cFlags8_5_35 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_35 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_102 coordinateInput8_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_102 hCoordinate8_83]
  decide +kernel
private abbrev cSpec8_5_36 := specAt8 5 36
private theorem cFlags8_5_36 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_36 = (List.replicate 8 false) := by
  rw [automaticFlags_cached _ _ coordinateInput8_82 coordinateInput8_103 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate8_82 hCoordinate8_103]
  decide +kernel
private abbrev cSpec8_5_37 := specAt8 5 37
private theorem cFlags8_5_37 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_37 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_37 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_37

private abbrev cSpec8_5_38 := specAt8 5 38
private theorem cFlags8_5_38 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_38 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_38 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_38

private abbrev cSpec8_5_39 := specAt8 5 39
private theorem cFlags8_5_39 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_39 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_39 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_39

private abbrev cSpec8_5_40 := specAt8 5 40
private theorem cFlags8_5_40 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_40 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_40 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_40

private abbrev cSpec8_5_41 := specAt8 5 41
private theorem cFlags8_5_41 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_41 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_20

private abbrev cSpec8_5_42 := specAt8 5 42
private theorem cFlags8_5_42 : automaticFlags (trunkCatalog.states 8).context cSpec8_5_42 = [false, true, false, false] := by
  exact (automaticFlags_same _ _ cSpec8_1_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_21

private abbrev cSpec8_6_1 := specAt8 6 1
private theorem cFlags8_6_1 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_1 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_1

private abbrev cSpec8_6_2 := specAt8 6 2
private theorem cFlags8_6_2 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_2 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec8_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_2

private abbrev cSpec8_6_3 := specAt8 6 3
private theorem cFlags8_6_3 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_3 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_3

private abbrev cSpec8_6_4 := specAt8 6 4
private theorem cFlags8_6_4 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_4 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_4

private abbrev cSpec8_6_5 := specAt8 6 5
private theorem cFlags8_6_5 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_5 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec8_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_5

private abbrev cSpec8_6_6 := specAt8 6 6
private theorem cFlags8_6_6 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_6 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_6

private abbrev cSpec8_6_7 := specAt8 6 7
private theorem cFlags8_6_7 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_7 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_7

private abbrev cSpec8_6_8 := specAt8 6 8
private theorem cFlags8_6_8 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_8 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_8

private abbrev cSpec8_6_9 := specAt8 6 9
private theorem cFlags8_6_9 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_9 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_9

private abbrev cSpec8_6_10 := specAt8 6 10
private theorem cFlags8_6_10 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_10 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_10

private abbrev cSpec8_6_11 := specAt8 6 11
private theorem cFlags8_6_11 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_11 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_5_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_5_11

private abbrev cSpec8_6_12 := specAt8 6 12
private theorem cFlags8_6_12 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_12 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec8_5_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_5_12

private abbrev cSpec8_6_13 := specAt8 6 13
private theorem cFlags8_6_13 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_13 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_5_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_5_13

private abbrev cSpec8_6_14 := specAt8 6 14
private theorem cFlags8_6_14 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_14 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_5_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_5_14

private abbrev cSpec8_6_15 := specAt8 6 15
private theorem cFlags8_6_15 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_15 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec8_5_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_5_15

private abbrev cSpec8_6_16 := specAt8 6 16
private theorem cFlags8_6_16 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_16 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_16

private abbrev cSpec8_6_17 := specAt8 6 17
private theorem cFlags8_6_17 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_17

private abbrev cSpec8_6_18 := specAt8 6 18
private theorem cFlags8_6_18 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_18 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_18

private abbrev cSpec8_6_19 := specAt8 6 19
private theorem cFlags8_6_19 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_19 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_19

private abbrev cSpec8_6_20 := specAt8 6 20
private theorem cFlags8_6_20 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_20 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_20

private abbrev cSpec8_6_21 := specAt8 6 21
private theorem cFlags8_6_21 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_21 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_21

private abbrev cSpec8_6_22 := specAt8 6 22
private theorem cFlags8_6_22 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_22 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_22

private abbrev cSpec8_6_23 := specAt8 6 23
private theorem cFlags8_6_23 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_23 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_23

private abbrev cSpec8_6_24 := specAt8 6 24
private theorem cFlags8_6_24 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_24 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_24

private abbrev cSpec8_6_25 := specAt8 6 25
private theorem cFlags8_6_25 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_25 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_25

private abbrev cSpec8_6_26 := specAt8 6 26
private theorem cFlags8_6_26 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_11

private abbrev cSpec8_6_27 := specAt8 6 27
private theorem cFlags8_6_27 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec8_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_12

private abbrev cSpec8_6_28 := specAt8 6 28
private theorem cFlags8_6_28 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_13

private abbrev cSpec8_6_29 := specAt8 6 29
private theorem cFlags8_6_29 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec8_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_14

private abbrev cSpec8_6_30 := specAt8 6 30
private theorem cFlags8_6_30 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_1_15

private abbrev cSpec8_6_31 := specAt8 6 31
private theorem cFlags8_6_31 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_31 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_2_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_16

private abbrev cSpec8_6_32 := specAt8 6 32
private theorem cFlags8_6_32 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_32 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_2_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_17

private abbrev cSpec8_6_33 := specAt8 6 33
private theorem cFlags8_6_33 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_33 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec8_2_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_18

private abbrev cSpec8_6_34 := specAt8 6 34
private theorem cFlags8_6_34 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_34 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_2_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_19

private abbrev cSpec8_6_35 := specAt8 6 35
private theorem cFlags8_6_35 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_35 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec8_2_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_20

private abbrev cSpec8_6_36 := specAt8 6 36
private theorem cFlags8_6_36 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_36 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_2_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_21

private abbrev cSpec8_6_37 := specAt8 6 37
private theorem cFlags8_6_37 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_37 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec8_2_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_22

private abbrev cSpec8_6_38 := specAt8 6 38
private theorem cFlags8_6_38 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_38 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_2_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_23

private abbrev cSpec8_6_39 := specAt8 6 39
private theorem cFlags8_6_39 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_39 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec8_2_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_24

private abbrev cSpec8_6_40 := specAt8 6 40
private theorem cFlags8_6_40 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_40 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec8_2_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_25

private abbrev cSpec8_6_41 := specAt8 6 41
private theorem cFlags8_6_41 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_41 = (List.replicate 8 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_31

private abbrev cSpec8_6_42 := specAt8 6 42
private theorem cFlags8_6_42 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_42 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_32

private abbrev cSpec8_6_43 := specAt8 6 43
private theorem cFlags8_6_43 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_43 = (List.replicate 8 true) := by
  exact (automaticFlags_same _ _ cSpec8_5_33 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_5_33

private abbrev cSpec8_6_44 := specAt8 6 44
private theorem cFlags8_6_44 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_44 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec8_5_34 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_5_34

private abbrev cSpec8_6_45 := specAt8 6 45
private theorem cFlags8_6_45 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_45 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec8_5_35 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_5_35

private abbrev cSpec8_6_46 := specAt8 6 46
private theorem cFlags8_6_46 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_46 = (List.replicate 8 false) := by
  exact (automaticFlags_same _ _ cSpec8_5_36 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_5_36

private abbrev cSpec8_6_47 := specAt8 6 47
private theorem cFlags8_6_47 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_47 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_3_37 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_37

private abbrev cSpec8_6_48 := specAt8 6 48
private theorem cFlags8_6_48 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_48 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_38 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_38

private abbrev cSpec8_6_49 := specAt8 6 49
private theorem cFlags8_6_49 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_49 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_39 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_39

private abbrev cSpec8_6_50 := specAt8 6 50
private theorem cFlags8_6_50 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_50 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec8_3_40 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_3_40

private abbrev cSpec8_6_51 := specAt8 6 51
private theorem cFlags8_6_51 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_51 = [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false] := by
  exact (automaticFlags_same _ _ cSpec8_2_30 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_30

private abbrev cSpec8_6_52 := specAt8 6 52
private theorem cFlags8_6_52 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_52 = (List.replicate 1 false) := by
  exact (automaticFlags_same _ _ cSpec8_2_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_31

private abbrev cSpec8_6_53 := specAt8 6 53
private theorem cFlags8_6_53 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_53 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec8_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_0_20

private abbrev cSpec8_6_54 := specAt8 6 54
private theorem cFlags8_6_54 : automaticFlags (trunkCatalog.states 8).context cSpec8_6_54 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec8_2_33 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags8_2_33

private theorem keys_eq : coverageKeys (trunkCatalog.states 8) = checkedKeys := by
  rfl
private theorem tasks_eq : coverageTasks (trunkCatalog.states 8) = checkedTasks := by
  rw [← coverageTasksProjection_eq]
  change [(0,[(1, (automaticFlags (trunkCatalog.states 8).context cSpec8_0_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 8).context cSpec8_0_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 8).context cSpec8_0_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 8).context cSpec8_0_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 8).context cSpec8_0_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 8).context cSpec8_0_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 8).context cSpec8_0_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 8).context cSpec8_0_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 8).context cSpec8_0_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 8).context cSpec8_0_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 8).context cSpec8_0_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 8).context cSpec8_0_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 8).context cSpec8_0_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 8).context cSpec8_0_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 8).context cSpec8_0_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 8).context cSpec8_0_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 8).context cSpec8_0_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 8).context cSpec8_0_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 8).context cSpec8_0_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 8).context cSpec8_0_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 8).context cSpec8_0_21).zipIdx.map Prod.swap)]),(1,[(1, (automaticFlags (trunkCatalog.states 8).context cSpec8_1_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 8).context cSpec8_1_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 8).context cSpec8_1_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 8).context cSpec8_1_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 8).context cSpec8_1_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 8).context cSpec8_1_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 8).context cSpec8_1_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 8).context cSpec8_1_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 8).context cSpec8_1_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 8).context cSpec8_1_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 8).context cSpec8_1_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 8).context cSpec8_1_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 8).context cSpec8_1_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 8).context cSpec8_1_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 8).context cSpec8_1_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 8).context cSpec8_1_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 8).context cSpec8_1_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 8).context cSpec8_1_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 8).context cSpec8_1_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 8).context cSpec8_1_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 8).context cSpec8_1_21).zipIdx.map Prod.swap)]),(2,[(1, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 8).context cSpec8_2_33).zipIdx.map Prod.swap)]),(3,[(1, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 8).context cSpec8_3_42).zipIdx.map Prod.swap)]),(4,[(1, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_42).zipIdx.map Prod.swap),(43, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_43).zipIdx.map Prod.swap),(44, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_44).zipIdx.map Prod.swap),(45, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_45).zipIdx.map Prod.swap),(46, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_46).zipIdx.map Prod.swap),(47, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_47).zipIdx.map Prod.swap),(48, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_48).zipIdx.map Prod.swap),(49, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_49).zipIdx.map Prod.swap),(50, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_50).zipIdx.map Prod.swap),(51, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_51).zipIdx.map Prod.swap),(52, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_52).zipIdx.map Prod.swap),(53, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_53).zipIdx.map Prod.swap),(54, (automaticFlags (trunkCatalog.states 8).context cSpec8_4_54).zipIdx.map Prod.swap)]),(5,[(1, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 8).context cSpec8_5_42).zipIdx.map Prod.swap)]),(6,[(1, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_42).zipIdx.map Prod.swap),(43, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_43).zipIdx.map Prod.swap),(44, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_44).zipIdx.map Prod.swap),(45, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_45).zipIdx.map Prod.swap),(46, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_46).zipIdx.map Prod.swap),(47, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_47).zipIdx.map Prod.swap),(48, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_48).zipIdx.map Prod.swap),(49, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_49).zipIdx.map Prod.swap),(50, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_50).zipIdx.map Prod.swap),(51, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_51).zipIdx.map Prod.swap),(52, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_52).zipIdx.map Prod.swap),(53, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_53).zipIdx.map Prod.swap),(54, (automaticFlags (trunkCatalog.states 8).context cSpec8_6_54).zipIdx.map Prod.swap)])] = checkedTasks
  rw [cFlags8_0_1, cFlags8_0_2, cFlags8_0_3, cFlags8_0_4, cFlags8_0_5, cFlags8_0_6, cFlags8_0_7, cFlags8_0_8, cFlags8_0_9, cFlags8_0_10, cFlags8_0_11, cFlags8_0_12, cFlags8_0_13, cFlags8_0_14, cFlags8_0_15, cFlags8_0_16, cFlags8_0_17, cFlags8_0_18, cFlags8_0_19, cFlags8_0_20, cFlags8_0_21, cFlags8_1_1, cFlags8_1_2, cFlags8_1_3, cFlags8_1_4, cFlags8_1_5, cFlags8_1_6, cFlags8_1_7, cFlags8_1_8, cFlags8_1_9, cFlags8_1_10, cFlags8_1_11, cFlags8_1_12, cFlags8_1_13, cFlags8_1_14, cFlags8_1_15, cFlags8_1_16, cFlags8_1_17, cFlags8_1_18, cFlags8_1_19, cFlags8_1_20, cFlags8_1_21, cFlags8_2_1, cFlags8_2_2, cFlags8_2_3, cFlags8_2_4, cFlags8_2_5, cFlags8_2_6, cFlags8_2_7, cFlags8_2_8, cFlags8_2_9, cFlags8_2_10, cFlags8_2_11, cFlags8_2_12, cFlags8_2_13, cFlags8_2_14, cFlags8_2_15, cFlags8_2_16, cFlags8_2_17, cFlags8_2_18, cFlags8_2_19, cFlags8_2_20, cFlags8_2_21, cFlags8_2_22, cFlags8_2_23, cFlags8_2_24, cFlags8_2_25, cFlags8_2_26, cFlags8_2_27, cFlags8_2_28, cFlags8_2_29, cFlags8_2_30, cFlags8_2_31, cFlags8_2_32, cFlags8_2_33, cFlags8_3_1, cFlags8_3_2, cFlags8_3_3, cFlags8_3_4, cFlags8_3_5, cFlags8_3_6, cFlags8_3_7, cFlags8_3_8, cFlags8_3_9, cFlags8_3_10, cFlags8_3_11, cFlags8_3_12, cFlags8_3_13, cFlags8_3_14, cFlags8_3_15, cFlags8_3_16, cFlags8_3_17, cFlags8_3_18, cFlags8_3_19, cFlags8_3_20, cFlags8_3_21, cFlags8_3_22, cFlags8_3_23, cFlags8_3_24, cFlags8_3_25, cFlags8_3_26, cFlags8_3_27, cFlags8_3_28, cFlags8_3_29, cFlags8_3_30, cFlags8_3_31, cFlags8_3_32, cFlags8_3_33, cFlags8_3_34, cFlags8_3_35, cFlags8_3_36, cFlags8_3_37, cFlags8_3_38, cFlags8_3_39, cFlags8_3_40, cFlags8_3_41, cFlags8_3_42, cFlags8_4_1, cFlags8_4_2, cFlags8_4_3, cFlags8_4_4, cFlags8_4_5, cFlags8_4_6, cFlags8_4_7, cFlags8_4_8, cFlags8_4_9, cFlags8_4_10, cFlags8_4_11, cFlags8_4_12, cFlags8_4_13, cFlags8_4_14, cFlags8_4_15, cFlags8_4_16, cFlags8_4_17, cFlags8_4_18, cFlags8_4_19, cFlags8_4_20, cFlags8_4_21, cFlags8_4_22, cFlags8_4_23, cFlags8_4_24, cFlags8_4_25, cFlags8_4_26, cFlags8_4_27, cFlags8_4_28, cFlags8_4_29, cFlags8_4_30, cFlags8_4_31, cFlags8_4_32, cFlags8_4_33, cFlags8_4_34, cFlags8_4_35, cFlags8_4_36, cFlags8_4_37, cFlags8_4_38, cFlags8_4_39, cFlags8_4_40, cFlags8_4_41, cFlags8_4_42, cFlags8_4_43, cFlags8_4_44, cFlags8_4_45, cFlags8_4_46, cFlags8_4_47, cFlags8_4_48, cFlags8_4_49, cFlags8_4_50, cFlags8_4_51, cFlags8_4_52, cFlags8_4_53, cFlags8_4_54, cFlags8_5_1, cFlags8_5_2, cFlags8_5_3, cFlags8_5_4, cFlags8_5_5, cFlags8_5_6, cFlags8_5_7, cFlags8_5_8, cFlags8_5_9, cFlags8_5_10, cFlags8_5_11, cFlags8_5_12, cFlags8_5_13, cFlags8_5_14, cFlags8_5_15, cFlags8_5_16, cFlags8_5_17, cFlags8_5_18, cFlags8_5_19, cFlags8_5_20, cFlags8_5_21, cFlags8_5_22, cFlags8_5_23, cFlags8_5_24, cFlags8_5_25, cFlags8_5_26, cFlags8_5_27, cFlags8_5_28, cFlags8_5_29, cFlags8_5_30, cFlags8_5_31, cFlags8_5_32, cFlags8_5_33, cFlags8_5_34, cFlags8_5_35, cFlags8_5_36, cFlags8_5_37, cFlags8_5_38, cFlags8_5_39, cFlags8_5_40, cFlags8_5_41, cFlags8_5_42, cFlags8_6_1, cFlags8_6_2, cFlags8_6_3, cFlags8_6_4, cFlags8_6_5, cFlags8_6_6, cFlags8_6_7, cFlags8_6_8, cFlags8_6_9, cFlags8_6_10, cFlags8_6_11, cFlags8_6_12, cFlags8_6_13, cFlags8_6_14, cFlags8_6_15, cFlags8_6_16, cFlags8_6_17, cFlags8_6_18, cFlags8_6_19, cFlags8_6_20, cFlags8_6_21, cFlags8_6_22, cFlags8_6_23, cFlags8_6_24, cFlags8_6_25, cFlags8_6_26, cFlags8_6_27, cFlags8_6_28, cFlags8_6_29, cFlags8_6_30, cFlags8_6_31, cFlags8_6_32, cFlags8_6_33, cFlags8_6_34, cFlags8_6_35, cFlags8_6_36, cFlags8_6_37, cFlags8_6_38, cFlags8_6_39, cFlags8_6_40, cFlags8_6_41, cFlags8_6_42, cFlags8_6_43, cFlags8_6_44, cFlags8_6_45, cFlags8_6_46, cFlags8_6_47, cFlags8_6_48, cFlags8_6_49, cFlags8_6_50, cFlags8_6_51, cFlags8_6_52, cFlags8_6_53, cFlags8_6_54]
  rfl
private theorem parents_length : (trunkRawParents (trunkCatalog.states 8).context).length = 250 := by
  decide +kernel
private theorem table_checked : coverageTable checkedKeys checkedTasks 250 := by
  apply coverageRemainder_sound _ _ _ [[74, 124], [199, 249], [124, 149, 199, 249], [199], [199], [199], []]
  unfold coverageRemainder parentsFor
  decide +kernel

theorem solution : trunkCoverage trunkCatalog 8 := by
  apply coverageTable_sound 8
  · unfold certRectangleValid; decide +kernel
  · decide +kernel
  · rw [keys_eq, tasks_eq, parents_length]
    exact table_checked
#print axioms solution
