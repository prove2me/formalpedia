-- Prove2me | solution 1 for Freiman.trunk_coverage_02
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:44:37.107189+00:00
-- url     : https://prove2.me/submissions/f53f60c0-bf7a-4881-ba7c-317d09c11c55

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

private def coordinateFields2 : Array CertField := #[⟨(4/13),(1/13),(0/1),(0/1)⟩,⟨(52/73),(1/73),(0/1),(0/1)⟩,⟨(9/13),(-1/13),(0/1),(0/1)⟩,⟨(2/1),(-1/1),(0/1),(0/1)⟩,⟨(15/37),(-1/37),(0/1),(0/1)⟩,⟨(125/214),(-1/214),(0/1),(0/1)⟩,⟨(1/2),(1/6),(0/1),(0/1)⟩,⟨(66/179),(-1/537),(0/1),(0/1)⟩,⟨(22/37),(1/37),(0/1),(0/1)⟩,⟨(17/22),(-1/22),(0/1),(0/1)⟩,⟨(101/143),(-1/429),(0/1),(0/1)⟩,⟨(89/214),(1/214),(0/1),(0/1)⟩,⟨(35/94),(1/94),(0/1),(0/1)⟩,⟨(10/23),(-1/69),(0/1),(0/1)⟩,⟨(517/1249),(-1/1249),(0/1),(0/1)⟩,⟨(5/22),(1/22),(0/1),(0/1)⟩,⟨(271/1006),(-1/1006),(0/1),(0/1)⟩,⟨(16/59),(1/177),(0/1),(0/1)⟩,⟨(43/142),(-1/142),(0/1),(0/1)⟩,⟨(731/2497),(-1/2497),(0/1),(0/1)⟩,⟨(42/143),(1/429),(0/1),(0/1)⟩,⟨(767/2749),(1/2749),(0/1),(0/1)⟩,⟨(1809/6094),(1/6094),(0/1),(0/1)⟩,⟨(553/1429),(1/1429),(0/1),(0/1)⟩,⟨(1272/3013),(1/3013),(0/1),(0/1)⟩,⟨(3289/10753),(1/10753),(0/1),(0/1)⟩,⟨(71/229),(-1/229),(0/1),(0/1)⟩,⟨(1413/4654),(-1/4654),(0/1),(0/1)⟩,⟨(6697/22079),(-1/66237),(0/1),(0/1)⟩,⟨(469/1549),(1/1549),(0/1),(0/1)⟩,⟨(579/1894),(-1/1894),(0/1),(0/1)⟩,⟨(9014/29557),(-1/29557),(0/1),(0/1)⟩,⟨(113/179),(1/537),(0/1),(0/1)⟩,⟨(735/1006),(1/1006),(0/1),(0/1)⟩,⟨(13/23),(1/69),(0/1),(0/1)⟩,⟨(732/1249),(1/1249),(0/1),(0/1)⟩,⟨(59/94),(-1/94),(0/1),(0/1)⟩]
private abbrev coordinateInput2_0 : LowerPair × Bool × Bool := (([2], []), true, false)
private def coordinateCodes2_0 : List (ℕ × ℕ) := [(0, 1), (0, 1)]
private abbrev coordinateInput2_1 : LowerPair × Bool × Bool := (([1], []), false, false)
private def coordinateCodes2_1 : List (ℕ × ℕ) := [(2, 3), (2, 4), (2, 3), (5, 3), (2, 3)]
private abbrev coordinateInput2_2 : LowerPair × Bool × Bool := (([1], []), true, false)
private def coordinateCodes2_2 : List (ℕ × ℕ) := [(6, 1), (6, 1)]
private abbrev coordinateInput2_3 : LowerPair × Bool × Bool := (([2], []), false, false)
private def coordinateCodes2_3 : List (ℕ × ℕ) := [(4, 3), (4, 4), (4, 3), (7, 3), (4, 3)]
private abbrev coordinateInput2_4 : LowerPair × Bool × Bool := (([1, 1], []), true, false)
private def coordinateCodes2_4 : List (ℕ × ℕ) := [(8, 1)]
private abbrev coordinateInput2_5 : LowerPair × Bool × Bool := (([1, 2], []), false, false)
private def coordinateCodes2_5 : List (ℕ × ℕ) := [(9, 3), (9, 4), (9, 3), (10, 3)]
private abbrev coordinateInput2_6 : LowerPair × Bool × Bool := (([1, 2], []), true, false)
private def coordinateCodes2_6 : List (ℕ × ℕ) := [(1, 1)]
private abbrev coordinateInput2_7 : LowerPair × Bool × Bool := (([1, 1], []), false, false)
private def coordinateCodes2_7 : List (ℕ × ℕ) := [(2, 3), (2, 4), (2, 3), (5, 3)]
private abbrev coordinateInput2_8 : LowerPair × Bool × Bool := (([1], [1]), true, true)
private def coordinateCodes2_8 : List (ℕ × ℕ) := [(6, 1)]
private abbrev coordinateInput2_9 : LowerPair × Bool × Bool := (([1], [2]), false, true)
private def coordinateCodes2_9 : List (ℕ × ℕ) := [(2, 4), (2, 7), (2, 4), (5, 4)]
private abbrev coordinateInput2_10 : LowerPair × Bool × Bool := (([1], [2]), true, true)
private def coordinateCodes2_10 : List (ℕ × ℕ) := [(6, 0), (6, 11), (6, 0), (1, 0)]
private abbrev coordinateInput2_11 : LowerPair × Bool × Bool := (([1], [1]), false, true)
private def coordinateCodes2_11 : List (ℕ × ℕ) := [(2, 2), (2, 5), (2, 2), (5, 2)]
private abbrev coordinateInput2_12 : LowerPair × Bool × Bool := (([2, 1], []), true, false)
private def coordinateCodes2_12 : List (ℕ × ℕ) := [(12, 1)]
private abbrev coordinateInput2_13 : LowerPair × Bool × Bool := (([2, 2], []), false, false)
private def coordinateCodes2_13 : List (ℕ × ℕ) := [(13, 3), (13, 4), (13, 3), (14, 3)]
private abbrev coordinateInput2_14 : LowerPair × Bool × Bool := (([2, 2], []), true, false)
private def coordinateCodes2_14 : List (ℕ × ℕ) := [(11, 1)]
private abbrev coordinateInput2_15 : LowerPair × Bool × Bool := (([2, 1], []), false, false)
private def coordinateCodes2_15 : List (ℕ × ℕ) := [(4, 3), (4, 4), (4, 3), (7, 3)]
private abbrev coordinateInput2_16 : LowerPair × Bool × Bool := (([2], [1]), true, true)
private def coordinateCodes2_16 : List (ℕ × ℕ) := [(0, 1)]
private abbrev coordinateInput2_17 : LowerPair × Bool × Bool := (([2], [2]), false, true)
private def coordinateCodes2_17 : List (ℕ × ℕ) := [(4, 4), (4, 7), (4, 4), (7, 4)]
private abbrev coordinateInput2_18 : LowerPair × Bool × Bool := (([2], [2]), true, true)
private def coordinateCodes2_18 : List (ℕ × ℕ) := [(0, 0), (0, 11), (0, 0), (11, 0)]
private abbrev coordinateInput2_19 : LowerPair × Bool × Bool := (([2], [1]), false, true)
private def coordinateCodes2_19 : List (ℕ × ℕ) := [(4, 2), (4, 5), (4, 2), (7, 2)]
private abbrev coordinateInput2_20 : LowerPair × Bool × Bool := (([3], []), true, false)
private def coordinateCodes2_20 : List (ℕ × ℕ) := [(15, 1), (15, 1)]
private abbrev coordinateInput2_21 : LowerPair × Bool × Bool := (([3], []), false, false)
private def coordinateCodes2_21 : List (ℕ × ℕ) := [(16, 3), (16, 3)]
private abbrev coordinateInput2_22 : LowerPair × Bool × Bool := (([3, 1], []), true, false)
private def coordinateCodes2_22 : List (ℕ × ℕ) := [(17, 1)]
private abbrev coordinateInput2_23 : LowerPair × Bool × Bool := (([3, 2], []), false, false)
private def coordinateCodes2_23 : List (ℕ × ℕ) := [(18, 3), (18, 4), (18, 3), (19, 3)]
private abbrev coordinateInput2_24 : LowerPair × Bool × Bool := (([3, 2], []), true, false)
private def coordinateCodes2_24 : List (ℕ × ℕ) := [(20, 1)]
private abbrev coordinateInput2_25 : LowerPair × Bool × Bool := (([3, 1], []), false, false)
private def coordinateCodes2_25 : List (ℕ × ℕ) := [(16, 3)]
private abbrev coordinateInput2_26 : LowerPair × Bool × Bool := (([3], [1]), true, true)
private def coordinateCodes2_26 : List (ℕ × ℕ) := [(15, 1)]
private abbrev coordinateInput2_27 : LowerPair × Bool × Bool := (([3], [2]), false, true)
private def coordinateCodes2_27 : List (ℕ × ℕ) := [(16, 4)]
private abbrev coordinateInput2_28 : LowerPair × Bool × Bool := (([3], [2]), true, true)
private def coordinateCodes2_28 : List (ℕ × ℕ) := [(15, 0), (15, 11), (15, 0), (20, 0)]
private abbrev coordinateInput2_29 : LowerPair × Bool × Bool := (([3], [1]), false, true)
private def coordinateCodes2_29 : List (ℕ × ℕ) := [(16, 2)]
private abbrev coordinateInput2_30 : LowerPair × Bool × Bool := (([], []), true, false)
private def coordinateCodes2_30 : List (ℕ × ℕ) := [(6, 1)]
private abbrev coordinateInput2_31 : LowerPair × Bool × Bool := (([], []), false, false)
private def coordinateCodes2_31 : List (ℕ × ℕ) := [(3, 3), (3, 4), (3, 3), (4, 3)]
private abbrev coordinateInput2_32 : LowerPair × Bool × Bool := (([3], [2]), true, false)
private def coordinateCodes2_32 : List (ℕ × ℕ) := [(15, 0), (15, 11), (15, 0), (20, 0)]
private abbrev coordinateInput2_33 : LowerPair × Bool × Bool := (([3], [2]), false, false)
private def coordinateCodes2_33 : List (ℕ × ℕ) := [(16, 4)]
private abbrev coordinateInput2_34 : LowerPair × Bool × Bool := (([3, 1], [2]), true, false)
private def coordinateCodes2_34 : List (ℕ × ℕ) := [(17, 0), (17, 11), (17, 0), (21, 0), (17, 0)]
private abbrev coordinateInput2_35 : LowerPair × Bool × Bool := (([3, 2], [2]), false, false)
private def coordinateCodes2_35 : List (ℕ × ℕ) := [(18, 4), (18, 4), (18, 7), (18, 4), (19, 4)]
private abbrev coordinateInput2_36 : LowerPair × Bool × Bool := (([3, 2], [2]), true, false)
private def coordinateCodes2_36 : List (ℕ × ℕ) := [(20, 0), (20, 11), (20, 0), (22, 0), (20, 0)]
private abbrev coordinateInput2_37 : LowerPair × Bool × Bool := (([3, 1], [2]), false, false)
private def coordinateCodes2_37 : List (ℕ × ℕ) := [(16, 4), (16, 4)]
private abbrev coordinateInput2_38 : LowerPair × Bool × Bool := (([3], [2, 1]), true, true)
private def coordinateCodes2_38 : List (ℕ × ℕ) := [(15, 12), (15, 12), (15, 23), (15, 12), (20, 12)]
private abbrev coordinateInput2_39 : LowerPair × Bool × Bool := (([3], [2, 2]), false, true)
private def coordinateCodes2_39 : List (ℕ × ℕ) := [(16, 13), (16, 13)]
private abbrev coordinateInput2_40 : LowerPair × Bool × Bool := (([3], [2, 2]), true, true)
private def coordinateCodes2_40 : List (ℕ × ℕ) := [(15, 11), (15, 11), (15, 24), (15, 11), (20, 11)]
private abbrev coordinateInput2_41 : LowerPair × Bool × Bool := (([3], [2, 1]), false, true)
private def coordinateCodes2_41 : List (ℕ × ℕ) := [(16, 4), (16, 4)]
private abbrev coordinateInput2_42 : LowerPair × Bool × Bool := (([3, 3], [3, 3]), true, false)
private def coordinateCodes2_42 : List (ℕ × ℕ) := [(25, 25)]
private abbrev coordinateInput2_43 : LowerPair × Bool × Bool := (([3, 3], [3, 3]), false, false)
private def coordinateCodes2_43 : List (ℕ × ℕ) := [(26, 26), (26, 27), (26, 26), (27, 26)]
private abbrev coordinateInput2_44 : LowerPair × Bool × Bool := (([3, 3, 1], [3, 3]), true, false)
private def coordinateCodes2_44 : List (ℕ × ℕ) := [(25, 25), (25, 25)]
private abbrev coordinateInput2_45 : LowerPair × Bool × Bool := (([3, 3, 2], [3, 3]), false, false)
private def coordinateCodes2_45 : List (ℕ × ℕ) := [(27, 26), (27, 27), (27, 26), (28, 26), (27, 26)]
private abbrev coordinateInput2_46 : LowerPair × Bool × Bool := (([3, 3, 2], [3, 3]), true, false)
private def coordinateCodes2_46 : List (ℕ × ℕ) := [(29, 25), (29, 25)]
private abbrev coordinateInput2_47 : LowerPair × Bool × Bool := (([3, 3, 1], [3, 3]), false, false)
private def coordinateCodes2_47 : List (ℕ × ℕ) := [(30, 26), (30, 27), (30, 26), (31, 26), (30, 26)]
private abbrev coordinateInput2_48 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 1]), true, true)
private def coordinateCodes2_48 : List (ℕ × ℕ) := [(25, 25), (25, 25)]
private abbrev coordinateInput2_49 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 2]), false, true)
private def coordinateCodes2_49 : List (ℕ × ℕ) := [(26, 27), (26, 27), (26, 28), (26, 27), (27, 27)]
private abbrev coordinateInput2_50 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 2]), true, true)
private def coordinateCodes2_50 : List (ℕ × ℕ) := [(25, 29), (25, 29)]
private abbrev coordinateInput2_51 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 1]), false, true)
private def coordinateCodes2_51 : List (ℕ × ℕ) := [(26, 30), (26, 30), (26, 31), (26, 30), (27, 30)]
private abbrev coordinateInput2_52 : LowerPair × Bool × Bool := (([3], [3]), true, false)
private def coordinateCodes2_52 : List (ℕ × ℕ) := [(15, 15), (15, 20), (15, 15), (20, 15)]
private abbrev coordinateInput2_53 : LowerPair × Bool × Bool := (([3], [3]), false, false)
private def coordinateCodes2_53 : List (ℕ × ℕ) := [(16, 16)]
private abbrev coordinateInput2_54 : LowerPair × Bool × Bool := (([3, 1], [3]), true, false)
private def coordinateCodes2_54 : List (ℕ × ℕ) := [(17, 15), (17, 20), (17, 15), (21, 15), (17, 15)]
private abbrev coordinateInput2_55 : LowerPair × Bool × Bool := (([3, 2], [3]), false, false)
private def coordinateCodes2_55 : List (ℕ × ℕ) := [(18, 16), (18, 16)]
private abbrev coordinateInput2_56 : LowerPair × Bool × Bool := (([3, 2], [3]), true, false)
private def coordinateCodes2_56 : List (ℕ × ℕ) := [(20, 15), (20, 20), (20, 15), (22, 15), (20, 15)]
private abbrev coordinateInput2_57 : LowerPair × Bool × Bool := (([3, 1], [3]), false, false)
private def coordinateCodes2_57 : List (ℕ × ℕ) := [(16, 16), (16, 16)]
private abbrev coordinateInput2_58 : LowerPair × Bool × Bool := (([3], [3, 1]), true, true)
private def coordinateCodes2_58 : List (ℕ × ℕ) := [(15, 17), (15, 17), (15, 21), (15, 17), (20, 17)]
private abbrev coordinateInput2_59 : LowerPair × Bool × Bool := (([3], [3, 2]), false, true)
private def coordinateCodes2_59 : List (ℕ × ℕ) := [(16, 18), (16, 18)]
private abbrev coordinateInput2_60 : LowerPair × Bool × Bool := (([3], [3, 2]), true, true)
private def coordinateCodes2_60 : List (ℕ × ℕ) := [(15, 20), (15, 20), (15, 22), (15, 20), (20, 20)]
private abbrev coordinateInput2_61 : LowerPair × Bool × Bool := (([3], [3, 1]), false, true)
private def coordinateCodes2_61 : List (ℕ × ℕ) := [(16, 16), (16, 16)]
private abbrev coordinateInput2_62 : LowerPair × Bool × Bool := (([2], [1]), true, false)
private def coordinateCodes2_62 : List (ℕ × ℕ) := [(0, 1)]
private abbrev coordinateInput2_63 : LowerPair × Bool × Bool := (([2], [1]), false, false)
private def coordinateCodes2_63 : List (ℕ × ℕ) := [(4, 2), (4, 5), (4, 2), (7, 2)]
private abbrev coordinateInput2_64 : LowerPair × Bool × Bool := (([2, 1], [1]), true, false)
private def coordinateCodes2_64 : List (ℕ × ℕ) := [(12, 1), (12, 1)]
private abbrev coordinateInput2_65 : LowerPair × Bool × Bool := (([2, 2], [1]), false, false)
private def coordinateCodes2_65 : List (ℕ × ℕ) := [(13, 2), (13, 2), (13, 5), (13, 2), (14, 2)]
private abbrev coordinateInput2_66 : LowerPair × Bool × Bool := (([2, 2], [1]), true, false)
private def coordinateCodes2_66 : List (ℕ × ℕ) := [(11, 1), (11, 1)]
private abbrev coordinateInput2_67 : LowerPair × Bool × Bool := (([2, 1], [1]), false, false)
private def coordinateCodes2_67 : List (ℕ × ℕ) := [(4, 2), (4, 2), (4, 5), (4, 2), (7, 2)]
private abbrev coordinateInput2_68 : LowerPair × Bool × Bool := (([2], [1, 1]), true, true)
private def coordinateCodes2_68 : List (ℕ × ℕ) := [(0, 8), (0, 8), (0, 32), (0, 8), (11, 8)]
private abbrev coordinateInput2_69 : LowerPair × Bool × Bool := (([2], [1, 2]), false, true)
private def coordinateCodes2_69 : List (ℕ × ℕ) := [(4, 9), (4, 10), (4, 9), (7, 9), (4, 9)]
private abbrev coordinateInput2_70 : LowerPair × Bool × Bool := (([2], [1, 2]), true, true)
private def coordinateCodes2_70 : List (ℕ × ℕ) := [(0, 1), (0, 1), (0, 33), (0, 1), (11, 1)]
private abbrev coordinateInput2_71 : LowerPair × Bool × Bool := (([2], [1, 1]), false, true)
private def coordinateCodes2_71 : List (ℕ × ℕ) := [(4, 2), (4, 5), (4, 2), (7, 2), (4, 2)]
private abbrev coordinateInput2_72 : LowerPair × Bool × Bool := (([3], [1]), true, false)
private def coordinateCodes2_72 : List (ℕ × ℕ) := [(15, 1)]
private abbrev coordinateInput2_73 : LowerPair × Bool × Bool := (([3], [1]), false, false)
private def coordinateCodes2_73 : List (ℕ × ℕ) := [(16, 2)]
private abbrev coordinateInput2_74 : LowerPair × Bool × Bool := (([3, 1], [1]), true, false)
private def coordinateCodes2_74 : List (ℕ × ℕ) := [(17, 1), (17, 1)]
private abbrev coordinateInput2_75 : LowerPair × Bool × Bool := (([3, 2], [1]), false, false)
private def coordinateCodes2_75 : List (ℕ × ℕ) := [(18, 2), (18, 2), (18, 5), (18, 2), (19, 2)]
private abbrev coordinateInput2_76 : LowerPair × Bool × Bool := (([3, 2], [1]), true, false)
private def coordinateCodes2_76 : List (ℕ × ℕ) := [(20, 1), (20, 1)]
private abbrev coordinateInput2_77 : LowerPair × Bool × Bool := (([3, 1], [1]), false, false)
private def coordinateCodes2_77 : List (ℕ × ℕ) := [(16, 2), (16, 2)]
private abbrev coordinateInput2_78 : LowerPair × Bool × Bool := (([3], [1, 1]), true, true)
private def coordinateCodes2_78 : List (ℕ × ℕ) := [(15, 8), (15, 8), (15, 32), (15, 8), (20, 8)]
private abbrev coordinateInput2_79 : LowerPair × Bool × Bool := (([3], [1, 2]), false, true)
private def coordinateCodes2_79 : List (ℕ × ℕ) := [(16, 9), (16, 9)]
private abbrev coordinateInput2_80 : LowerPair × Bool × Bool := (([3], [1, 2]), true, true)
private def coordinateCodes2_80 : List (ℕ × ℕ) := [(15, 1), (15, 1), (15, 33), (15, 1), (20, 1)]
private abbrev coordinateInput2_81 : LowerPair × Bool × Bool := (([3], [1, 1]), false, true)
private def coordinateCodes2_81 : List (ℕ × ℕ) := [(16, 2), (16, 2)]
private abbrev coordinateInput2_82 : LowerPair × Bool × Bool := (([2], [2]), true, false)
private def coordinateCodes2_82 : List (ℕ × ℕ) := [(0, 0), (0, 11), (0, 0), (11, 0)]
private abbrev coordinateInput2_83 : LowerPair × Bool × Bool := (([2], [2]), false, false)
private def coordinateCodes2_83 : List (ℕ × ℕ) := [(4, 4), (4, 7), (4, 4), (7, 4)]
private abbrev coordinateInput2_84 : LowerPair × Bool × Bool := (([2, 1], [2]), true, false)
private def coordinateCodes2_84 : List (ℕ × ℕ) := [(12, 0), (12, 11), (12, 0), (23, 0), (12, 0)]
private abbrev coordinateInput2_85 : LowerPair × Bool × Bool := (([2, 2], [2]), false, false)
private def coordinateCodes2_85 : List (ℕ × ℕ) := [(13, 4), (13, 4), (13, 7), (13, 4), (14, 4)]
private abbrev coordinateInput2_86 : LowerPair × Bool × Bool := (([2, 2], [2]), true, false)
private def coordinateCodes2_86 : List (ℕ × ℕ) := [(11, 0), (11, 11), (11, 0), (24, 0), (11, 0)]
private abbrev coordinateInput2_87 : LowerPair × Bool × Bool := (([2, 1], [2]), false, false)
private def coordinateCodes2_87 : List (ℕ × ℕ) := [(4, 4), (4, 4), (4, 7), (4, 4), (7, 4)]
private abbrev coordinateInput2_88 : LowerPair × Bool × Bool := (([2], [2, 1]), true, true)
private def coordinateCodes2_88 : List (ℕ × ℕ) := [(0, 12), (0, 12), (0, 23), (0, 12), (11, 12)]
private abbrev coordinateInput2_89 : LowerPair × Bool × Bool := (([2], [2, 2]), false, true)
private def coordinateCodes2_89 : List (ℕ × ℕ) := [(4, 13), (4, 14), (4, 13), (7, 13), (4, 13)]
private abbrev coordinateInput2_90 : LowerPair × Bool × Bool := (([2], [2, 2]), true, true)
private def coordinateCodes2_90 : List (ℕ × ℕ) := [(0, 11), (0, 11), (0, 24), (0, 11), (11, 11)]
private abbrev coordinateInput2_91 : LowerPair × Bool × Bool := (([2], [2, 1]), false, true)
private def coordinateCodes2_91 : List (ℕ × ℕ) := [(4, 4), (4, 7), (4, 4), (7, 4), (4, 4)]
private abbrev coordinateInput2_92 : LowerPair × Bool × Bool := (([2], [3]), true, false)
private def coordinateCodes2_92 : List (ℕ × ℕ) := [(0, 15), (0, 20), (0, 15), (11, 15)]
private abbrev coordinateInput2_93 : LowerPair × Bool × Bool := (([2], [3]), false, false)
private def coordinateCodes2_93 : List (ℕ × ℕ) := [(4, 16)]
private abbrev coordinateInput2_94 : LowerPair × Bool × Bool := (([2, 1], [3]), true, false)
private def coordinateCodes2_94 : List (ℕ × ℕ) := [(12, 15), (12, 20), (12, 15), (23, 15), (12, 15)]
private abbrev coordinateInput2_95 : LowerPair × Bool × Bool := (([2, 2], [3]), false, false)
private def coordinateCodes2_95 : List (ℕ × ℕ) := [(13, 16), (13, 16)]
private abbrev coordinateInput2_96 : LowerPair × Bool × Bool := (([2, 2], [3]), true, false)
private def coordinateCodes2_96 : List (ℕ × ℕ) := [(11, 15), (11, 20), (11, 15), (24, 15), (11, 15)]
private abbrev coordinateInput2_97 : LowerPair × Bool × Bool := (([2, 1], [3]), false, false)
private def coordinateCodes2_97 : List (ℕ × ℕ) := [(4, 16), (4, 16)]
private abbrev coordinateInput2_98 : LowerPair × Bool × Bool := (([2], [3, 1]), true, true)
private def coordinateCodes2_98 : List (ℕ × ℕ) := [(0, 17), (0, 17), (0, 21), (0, 17), (11, 17)]
private abbrev coordinateInput2_99 : LowerPair × Bool × Bool := (([2], [3, 2]), false, true)
private def coordinateCodes2_99 : List (ℕ × ℕ) := [(4, 18), (4, 19), (4, 18), (7, 18), (4, 18)]
private abbrev coordinateInput2_100 : LowerPair × Bool × Bool := (([2], [3, 2]), true, true)
private def coordinateCodes2_100 : List (ℕ × ℕ) := [(0, 20), (0, 20), (0, 22), (0, 20), (11, 20)]
private abbrev coordinateInput2_101 : LowerPair × Bool × Bool := (([2], [3, 1]), false, true)
private def coordinateCodes2_101 : List (ℕ × ℕ) := [(4, 16), (4, 16)]
private abbrev coordinateInput2_102 : LowerPair × Bool × Bool := (([3], [1, 1]), true, false)
private def coordinateCodes2_102 : List (ℕ × ℕ) := [(15, 8), (15, 8), (15, 32), (15, 8), (20, 8)]
private abbrev coordinateInput2_103 : LowerPair × Bool × Bool := (([3], [1, 1]), false, false)
private def coordinateCodes2_103 : List (ℕ × ℕ) := [(16, 2), (16, 2)]
private abbrev coordinateInput2_104 : LowerPair × Bool × Bool := (([3, 1], [1, 1]), true, false)
private def coordinateCodes2_104 : List (ℕ × ℕ) := [(17, 8), (17, 32), (17, 8), (21, 8)]
private abbrev coordinateInput2_105 : LowerPair × Bool × Bool := (([3, 2], [1, 1]), false, false)
private def coordinateCodes2_105 : List (ℕ × ℕ) := [(18, 2), (18, 5), (18, 2), (19, 2)]
private abbrev coordinateInput2_106 : LowerPair × Bool × Bool := (([3, 2], [1, 1]), true, false)
private def coordinateCodes2_106 : List (ℕ × ℕ) := [(20, 8), (20, 32), (20, 8), (22, 8)]
private abbrev coordinateInput2_107 : LowerPair × Bool × Bool := (([3, 1], [1, 1]), false, false)
private def coordinateCodes2_107 : List (ℕ × ℕ) := [(16, 2)]
private abbrev coordinateInput2_108 : LowerPair × Bool × Bool := (([3], [1, 1, 1]), true, true)
private def coordinateCodes2_108 : List (ℕ × ℕ) := [(15, 8), (15, 32), (15, 8), (20, 8)]
private abbrev coordinateInput2_109 : LowerPair × Bool × Bool := (([3], [1, 1, 2]), false, true)
private def coordinateCodes2_109 : List (ℕ × ℕ) := [(16, 5)]
private abbrev coordinateInput2_110 : LowerPair × Bool × Bool := (([3], [1, 1, 2]), true, true)
private def coordinateCodes2_110 : List (ℕ × ℕ) := [(15, 34), (15, 35), (15, 34), (20, 34)]
private abbrev coordinateInput2_111 : LowerPair × Bool × Bool := (([3], [1, 1, 1]), false, true)
private def coordinateCodes2_111 : List (ℕ × ℕ) := [(16, 36)]

private def decodeCoordinate2 (x : ℕ × ℕ) : CertField × CertField :=
  (coordinateFields2[x.1]?.getD ⟨0,0,0,0⟩,coordinateFields2[x.2]?.getD ⟨0,0,0,0⟩)

private theorem hCoordinate2_0 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_0.1 coordinateInput2_0.2.1 coordinateInput2_0.2.2).map Prod.fst = coordinateCodes2_0.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_1 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_1.1 coordinateInput2_1.2.1 coordinateInput2_1.2.2).map Prod.fst = coordinateCodes2_1.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_2 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_2.1 coordinateInput2_2.2.1 coordinateInput2_2.2.2).map Prod.fst = coordinateCodes2_2.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_3 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_3.1 coordinateInput2_3.2.1 coordinateInput2_3.2.2).map Prod.fst = coordinateCodes2_3.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_4 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_4.1 coordinateInput2_4.2.1 coordinateInput2_4.2.2).map Prod.fst = coordinateCodes2_4.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_5 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_5.1 coordinateInput2_5.2.1 coordinateInput2_5.2.2).map Prod.fst = coordinateCodes2_5.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_6 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_6.1 coordinateInput2_6.2.1 coordinateInput2_6.2.2).map Prod.fst = coordinateCodes2_6.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_7 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_7.1 coordinateInput2_7.2.1 coordinateInput2_7.2.2).map Prod.fst = coordinateCodes2_7.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_8 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_8.1 coordinateInput2_8.2.1 coordinateInput2_8.2.2).map Prod.fst = coordinateCodes2_8.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_9 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_9.1 coordinateInput2_9.2.1 coordinateInput2_9.2.2).map Prod.fst = coordinateCodes2_9.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_10 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_10.1 coordinateInput2_10.2.1 coordinateInput2_10.2.2).map Prod.fst = coordinateCodes2_10.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_11 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_11.1 coordinateInput2_11.2.1 coordinateInput2_11.2.2).map Prod.fst = coordinateCodes2_11.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_12 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_12.1 coordinateInput2_12.2.1 coordinateInput2_12.2.2).map Prod.fst = coordinateCodes2_12.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_13 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_13.1 coordinateInput2_13.2.1 coordinateInput2_13.2.2).map Prod.fst = coordinateCodes2_13.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_14 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_14.1 coordinateInput2_14.2.1 coordinateInput2_14.2.2).map Prod.fst = coordinateCodes2_14.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_15 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_15.1 coordinateInput2_15.2.1 coordinateInput2_15.2.2).map Prod.fst = coordinateCodes2_15.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_16 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_16.1 coordinateInput2_16.2.1 coordinateInput2_16.2.2).map Prod.fst = coordinateCodes2_16.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_17 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_17.1 coordinateInput2_17.2.1 coordinateInput2_17.2.2).map Prod.fst = coordinateCodes2_17.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_18 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_18.1 coordinateInput2_18.2.1 coordinateInput2_18.2.2).map Prod.fst = coordinateCodes2_18.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_19 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_19.1 coordinateInput2_19.2.1 coordinateInput2_19.2.2).map Prod.fst = coordinateCodes2_19.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_20 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_20.1 coordinateInput2_20.2.1 coordinateInput2_20.2.2).map Prod.fst = coordinateCodes2_20.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_21 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_21.1 coordinateInput2_21.2.1 coordinateInput2_21.2.2).map Prod.fst = coordinateCodes2_21.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_22 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_22.1 coordinateInput2_22.2.1 coordinateInput2_22.2.2).map Prod.fst = coordinateCodes2_22.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_23 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_23.1 coordinateInput2_23.2.1 coordinateInput2_23.2.2).map Prod.fst = coordinateCodes2_23.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_24 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_24.1 coordinateInput2_24.2.1 coordinateInput2_24.2.2).map Prod.fst = coordinateCodes2_24.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_25 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_25.1 coordinateInput2_25.2.1 coordinateInput2_25.2.2).map Prod.fst = coordinateCodes2_25.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_26 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_26.1 coordinateInput2_26.2.1 coordinateInput2_26.2.2).map Prod.fst = coordinateCodes2_26.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_27 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_27.1 coordinateInput2_27.2.1 coordinateInput2_27.2.2).map Prod.fst = coordinateCodes2_27.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_28 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_28.1 coordinateInput2_28.2.1 coordinateInput2_28.2.2).map Prod.fst = coordinateCodes2_28.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_29 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_29.1 coordinateInput2_29.2.1 coordinateInput2_29.2.2).map Prod.fst = coordinateCodes2_29.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_30 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_30.1 coordinateInput2_30.2.1 coordinateInput2_30.2.2).map Prod.fst = coordinateCodes2_30.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_31 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_31.1 coordinateInput2_31.2.1 coordinateInput2_31.2.2).map Prod.fst = coordinateCodes2_31.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_32 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_32.1 coordinateInput2_32.2.1 coordinateInput2_32.2.2).map Prod.fst = coordinateCodes2_32.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_33 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_33.1 coordinateInput2_33.2.1 coordinateInput2_33.2.2).map Prod.fst = coordinateCodes2_33.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_34 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_34.1 coordinateInput2_34.2.1 coordinateInput2_34.2.2).map Prod.fst = coordinateCodes2_34.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_35 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_35.1 coordinateInput2_35.2.1 coordinateInput2_35.2.2).map Prod.fst = coordinateCodes2_35.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_36 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_36.1 coordinateInput2_36.2.1 coordinateInput2_36.2.2).map Prod.fst = coordinateCodes2_36.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_37 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_37.1 coordinateInput2_37.2.1 coordinateInput2_37.2.2).map Prod.fst = coordinateCodes2_37.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_38 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_38.1 coordinateInput2_38.2.1 coordinateInput2_38.2.2).map Prod.fst = coordinateCodes2_38.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_39 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_39.1 coordinateInput2_39.2.1 coordinateInput2_39.2.2).map Prod.fst = coordinateCodes2_39.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_40 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_40.1 coordinateInput2_40.2.1 coordinateInput2_40.2.2).map Prod.fst = coordinateCodes2_40.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_41 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_41.1 coordinateInput2_41.2.1 coordinateInput2_41.2.2).map Prod.fst = coordinateCodes2_41.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_42 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_42.1 coordinateInput2_42.2.1 coordinateInput2_42.2.2).map Prod.fst = coordinateCodes2_42.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_43 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_43.1 coordinateInput2_43.2.1 coordinateInput2_43.2.2).map Prod.fst = coordinateCodes2_43.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_44 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_44.1 coordinateInput2_44.2.1 coordinateInput2_44.2.2).map Prod.fst = coordinateCodes2_44.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_45 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_45.1 coordinateInput2_45.2.1 coordinateInput2_45.2.2).map Prod.fst = coordinateCodes2_45.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_46 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_46.1 coordinateInput2_46.2.1 coordinateInput2_46.2.2).map Prod.fst = coordinateCodes2_46.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_47 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_47.1 coordinateInput2_47.2.1 coordinateInput2_47.2.2).map Prod.fst = coordinateCodes2_47.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_48 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_48.1 coordinateInput2_48.2.1 coordinateInput2_48.2.2).map Prod.fst = coordinateCodes2_48.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_49 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_49.1 coordinateInput2_49.2.1 coordinateInput2_49.2.2).map Prod.fst = coordinateCodes2_49.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_50 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_50.1 coordinateInput2_50.2.1 coordinateInput2_50.2.2).map Prod.fst = coordinateCodes2_50.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_51 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_51.1 coordinateInput2_51.2.1 coordinateInput2_51.2.2).map Prod.fst = coordinateCodes2_51.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_52 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_52.1 coordinateInput2_52.2.1 coordinateInput2_52.2.2).map Prod.fst = coordinateCodes2_52.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_53 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_53.1 coordinateInput2_53.2.1 coordinateInput2_53.2.2).map Prod.fst = coordinateCodes2_53.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_54 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_54.1 coordinateInput2_54.2.1 coordinateInput2_54.2.2).map Prod.fst = coordinateCodes2_54.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_55 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_55.1 coordinateInput2_55.2.1 coordinateInput2_55.2.2).map Prod.fst = coordinateCodes2_55.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_56 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_56.1 coordinateInput2_56.2.1 coordinateInput2_56.2.2).map Prod.fst = coordinateCodes2_56.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_57 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_57.1 coordinateInput2_57.2.1 coordinateInput2_57.2.2).map Prod.fst = coordinateCodes2_57.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_58 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_58.1 coordinateInput2_58.2.1 coordinateInput2_58.2.2).map Prod.fst = coordinateCodes2_58.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_59 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_59.1 coordinateInput2_59.2.1 coordinateInput2_59.2.2).map Prod.fst = coordinateCodes2_59.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_60 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_60.1 coordinateInput2_60.2.1 coordinateInput2_60.2.2).map Prod.fst = coordinateCodes2_60.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_61 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_61.1 coordinateInput2_61.2.1 coordinateInput2_61.2.2).map Prod.fst = coordinateCodes2_61.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_62 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_62.1 coordinateInput2_62.2.1 coordinateInput2_62.2.2).map Prod.fst = coordinateCodes2_62.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_63 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_63.1 coordinateInput2_63.2.1 coordinateInput2_63.2.2).map Prod.fst = coordinateCodes2_63.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_64 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_64.1 coordinateInput2_64.2.1 coordinateInput2_64.2.2).map Prod.fst = coordinateCodes2_64.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_65 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_65.1 coordinateInput2_65.2.1 coordinateInput2_65.2.2).map Prod.fst = coordinateCodes2_65.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_66 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_66.1 coordinateInput2_66.2.1 coordinateInput2_66.2.2).map Prod.fst = coordinateCodes2_66.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_67 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_67.1 coordinateInput2_67.2.1 coordinateInput2_67.2.2).map Prod.fst = coordinateCodes2_67.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_68 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_68.1 coordinateInput2_68.2.1 coordinateInput2_68.2.2).map Prod.fst = coordinateCodes2_68.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_69 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_69.1 coordinateInput2_69.2.1 coordinateInput2_69.2.2).map Prod.fst = coordinateCodes2_69.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_70 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_70.1 coordinateInput2_70.2.1 coordinateInput2_70.2.2).map Prod.fst = coordinateCodes2_70.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_71 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_71.1 coordinateInput2_71.2.1 coordinateInput2_71.2.2).map Prod.fst = coordinateCodes2_71.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_72 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_72.1 coordinateInput2_72.2.1 coordinateInput2_72.2.2).map Prod.fst = coordinateCodes2_72.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_73 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_73.1 coordinateInput2_73.2.1 coordinateInput2_73.2.2).map Prod.fst = coordinateCodes2_73.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_74 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_74.1 coordinateInput2_74.2.1 coordinateInput2_74.2.2).map Prod.fst = coordinateCodes2_74.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_75 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_75.1 coordinateInput2_75.2.1 coordinateInput2_75.2.2).map Prod.fst = coordinateCodes2_75.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_76 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_76.1 coordinateInput2_76.2.1 coordinateInput2_76.2.2).map Prod.fst = coordinateCodes2_76.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_77 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_77.1 coordinateInput2_77.2.1 coordinateInput2_77.2.2).map Prod.fst = coordinateCodes2_77.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_78 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_78.1 coordinateInput2_78.2.1 coordinateInput2_78.2.2).map Prod.fst = coordinateCodes2_78.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_79 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_79.1 coordinateInput2_79.2.1 coordinateInput2_79.2.2).map Prod.fst = coordinateCodes2_79.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_80 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_80.1 coordinateInput2_80.2.1 coordinateInput2_80.2.2).map Prod.fst = coordinateCodes2_80.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_81 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_81.1 coordinateInput2_81.2.1 coordinateInput2_81.2.2).map Prod.fst = coordinateCodes2_81.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_82 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_82.1 coordinateInput2_82.2.1 coordinateInput2_82.2.2).map Prod.fst = coordinateCodes2_82.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_83 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_83.1 coordinateInput2_83.2.1 coordinateInput2_83.2.2).map Prod.fst = coordinateCodes2_83.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_84 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_84.1 coordinateInput2_84.2.1 coordinateInput2_84.2.2).map Prod.fst = coordinateCodes2_84.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_85 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_85.1 coordinateInput2_85.2.1 coordinateInput2_85.2.2).map Prod.fst = coordinateCodes2_85.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_86 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_86.1 coordinateInput2_86.2.1 coordinateInput2_86.2.2).map Prod.fst = coordinateCodes2_86.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_87 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_87.1 coordinateInput2_87.2.1 coordinateInput2_87.2.2).map Prod.fst = coordinateCodes2_87.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_88 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_88.1 coordinateInput2_88.2.1 coordinateInput2_88.2.2).map Prod.fst = coordinateCodes2_88.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_89 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_89.1 coordinateInput2_89.2.1 coordinateInput2_89.2.2).map Prod.fst = coordinateCodes2_89.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_90 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_90.1 coordinateInput2_90.2.1 coordinateInput2_90.2.2).map Prod.fst = coordinateCodes2_90.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_91 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_91.1 coordinateInput2_91.2.1 coordinateInput2_91.2.2).map Prod.fst = coordinateCodes2_91.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_92 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_92.1 coordinateInput2_92.2.1 coordinateInput2_92.2.2).map Prod.fst = coordinateCodes2_92.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_93 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_93.1 coordinateInput2_93.2.1 coordinateInput2_93.2.2).map Prod.fst = coordinateCodes2_93.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_94 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_94.1 coordinateInput2_94.2.1 coordinateInput2_94.2.2).map Prod.fst = coordinateCodes2_94.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_95 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_95.1 coordinateInput2_95.2.1 coordinateInput2_95.2.2).map Prod.fst = coordinateCodes2_95.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_96 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_96.1 coordinateInput2_96.2.1 coordinateInput2_96.2.2).map Prod.fst = coordinateCodes2_96.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_97 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_97.1 coordinateInput2_97.2.1 coordinateInput2_97.2.2).map Prod.fst = coordinateCodes2_97.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_98 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_98.1 coordinateInput2_98.2.1 coordinateInput2_98.2.2).map Prod.fst = coordinateCodes2_98.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_99 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_99.1 coordinateInput2_99.2.1 coordinateInput2_99.2.2).map Prod.fst = coordinateCodes2_99.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_100 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_100.1 coordinateInput2_100.2.1 coordinateInput2_100.2.2).map Prod.fst = coordinateCodes2_100.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_101 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_101.1 coordinateInput2_101.2.1 coordinateInput2_101.2.2).map Prod.fst = coordinateCodes2_101.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_102 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_102.1 coordinateInput2_102.2.1 coordinateInput2_102.2.2).map Prod.fst = coordinateCodes2_102.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_103 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_103.1 coordinateInput2_103.2.1 coordinateInput2_103.2.2).map Prod.fst = coordinateCodes2_103.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_104 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_104.1 coordinateInput2_104.2.1 coordinateInput2_104.2.2).map Prod.fst = coordinateCodes2_104.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_105 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_105.1 coordinateInput2_105.2.1 coordinateInput2_105.2.2).map Prod.fst = coordinateCodes2_105.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_106 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_106.1 coordinateInput2_106.2.1 coordinateInput2_106.2.2).map Prod.fst = coordinateCodes2_106.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_107 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_107.1 coordinateInput2_107.2.1 coordinateInput2_107.2.2).map Prod.fst = coordinateCodes2_107.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_108 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_108.1 coordinateInput2_108.2.1 coordinateInput2_108.2.2).map Prod.fst = coordinateCodes2_108.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_109 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_109.1 coordinateInput2_109.2.1 coordinateInput2_109.2.2).map Prod.fst = coordinateCodes2_109.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_110 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_110.1 coordinateInput2_110.2.1 coordinateInput2_110.2.2).map Prod.fst = coordinateCodes2_110.map decodeCoordinate2 := by decide +kernel

private theorem hCoordinate2_111 :
    (trunkEndpointCases (trunkCatalog.states 2).context coordinateInput2_111.1 coordinateInput2_111.2.1 coordinateInput2_111.2.2).map Prod.fst = coordinateCodes2_111.map decodeCoordinate2 := by decide +kernel

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
(0,[2,3,54],0,[-1]),
(0,[4,14,24,34,49,50,51,52,53,60,61,62,63,70,71,72,73,80,81,82,83,95,96,97,98],0,[-1]),
(0,[5,6,7,8,9,15,16,17,18,19,25,26,27,28,29,35,36,37,38,39,40,41,42,43,44,55,56,57,58,59,65,66,67,68,69,75,76,77,78,79,85,86,87,88,89,90,91,92,93,94],0,[-1]),
(0,[10],0,[-1]),
(0,[11],0,[-1]),
(0,[12,64],0,[-1]),
(0,[13],0,[-1]),
(0,[22],0,[-1]),
(0,[23],0,[-1]),
(0,[30],0,[-1]),
(0,[31],0,[-1]),
(0,[32],0,[-1]),
(0,[33],0,[-1]),
(0,[45],0,[-1]),
(0,[46],0,[-1]),
(0,[47],0,[-1]),
(0,[48],0,[-1]),
(0,[74],2,[0,1,2,3]),
(0,[74],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[74,99],7,[0,1,2,3]),
(0,[74],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[74],12,[0,1,2,3]),
(0,[74],15,[0,1,2,3]),
(0,[74],17,[0,1,2,3,4,5,6,7,8,9]),
(0,[74],19,[0,1,2,3,4,5,6,7,8,9]),
(0,[84],0,[-1]),
(0,[99],2,[0,1,2,3]),
(0,[99],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[99],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[99],12,[0,1,2,3]),
(0,[99],15,[0,1,2,3]),
(0,[99],17,[0,1,2,3,4,5,6,7,8,9]),
(0,[99],19,[0,1,2,3,4,5,6,7,8,9]),
(1,[0,10,20,30,45],0,[-1]),
(1,[1,11,21,31,46],0,[-1]),
(1,[2,3,54],0,[-1]),
(1,[4,14,24,34,49,50,51,52,53,60,61,62,63,70,71,72,73,80,81,82,83,95,96,97,98],0,[-1]),
(1,[5,6,7,8,9,15,16,17,18,19,25,26,27,28,29,35,36,37,38,39,40,41,42,43,44,55,56,57,58,59,65,66,67,68,69,75,76,77,78,79,85,86,87,88,89,90,91,92,93,94],0,[-1]),
(1,[12,64],0,[-1]),
(1,[13,23,33,48],0,[-1]),
(1,[22,32,47],0,[-1]),
(1,[74],0,[-1]),
(1,[84],0,[-1]),
(1,[99],0,[-1]),
(2,[0,10,20,30,45],0,[-1]),
(2,[1,11,21,31,46],0,[-1]),
(2,[2,3,54],0,[-1]),
(2,[4,14,24,34,49,50,51,52,53,60,61,62,63,70,71,72,73,80,81,82,83,95,96,97,98],0,[-1]),
(2,[5,6,7,8,9,15,16,17,18,19,25,26,27,28,29,35,36,37,38,39,40,41,42,43,44,55,56,57,58,59,65,66,67,68,69,75,76,77,78,79,85,86,87,88,89,90,91,92,93,94],0,[-1]),
(2,[12,64],0,[-1]),
(2,[13,23,33,48],0,[-1]),
(2,[22,32,47],0,[-1]),
(2,[74],2,[0,1,2,3]),
(2,[74],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[74,99],7,[0,1,2,3]),
(2,[74],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[74,99],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[74],14,[0,1,2,3,4,5,6,7,8,9]),
(2,[74,99],18,[0,1,2,3,4,5,6,7,8,9]),
(2,[74],20,[0,1,2,3,4,5,6,7,8,9]),
(2,[74,99],22,[0,1,2,3,4,5,6,7,8,9]),
(2,[74],24,[0,1,2,3,4,5,6,7,8,9]),
(2,[74],27,[0,1,2,3,4,5,6,7,8,9]),
(2,[74],29,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]),
(2,[74,99],30,[12,13,14,15]),
(2,[74],31,[0]),
(2,[84],0,[-1]),
(2,[99],2,[0,1,2,3]),
(2,[99],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[99],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[99],14,[0,1,2,3,4,5,6,7,8,9]),
(2,[99],20,[0,1,2,3,4,5,6,7,8,9]),
(2,[99],24,[0,1,2,3,4,5,6,7,8,9]),
(2,[99],27,[0,1,2,3,4,5,6,7,8,9]),
(2,[99],29,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]),
(2,[99],31,[0]),
(3,[0,10,20,30,45],0,[-1]),
(3,[1,11,21,31,46],0,[-1]),
(3,[2,3,54],0,[-1]),
(3,[4,14,24,34,49,50,51,52,53,60,61,62,63,70,71,72,73,80,81,82,83,95,96,97,98],0,[-1]),
(3,[5,6,7,8,9,15,16,17,18,19,25,26,27,28,29,35,36,37,38,39,40,41,42,43,44,55,56,57,58,59,65,66,67,68,69,75,76,77,78,79,85,86,87,88,89,90,91,92,93,94],0,[-1]),
(3,[12,64],0,[-1]),
(3,[13,23,33,48],0,[-1]),
(3,[22,32,47],0,[-1]),
(3,[74],0,[-1]),
(3,[84],0,[-1]),
(3,[99],2,[0,1,2,3]),
(3,[99],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
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
(4,[2,3,54],0,[-1]),
(4,[4,14,24,34,49,50,51,52,53,60,61,62,63,70,71,72,73,80,81,82,83,95,96,97,98],0,[-1]),
(4,[5,6,7,8,9,15,16,17,18,19,25,26,27,28,29,35,36,37,38,39,40,41,42,43,44,55,56,57,58,59,65,66,67,68,69,75,76,77,78,79,85,86,87,88,89,90,91,92,93,94],0,[-1]),
(4,[12,64],0,[-1]),
(4,[13,23,33,48],0,[-1]),
(4,[22,32,47],0,[-1]),
(4,[74],0,[-1]),
(4,[84],0,[-1]),
(4,[99],2,[0,1,2,3]),
(4,[99],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
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
(5,[2,3,54],0,[-1]),
(5,[4,14,24,34,49,50,51,52,53,60,61,62,63,70,71,72,73,80,81,82,83,95,96,97,98],0,[-1]),
(5,[5,6,7,8,9,15,16,17,18,19,25,26,27,28,29,35,36,37,38,39,40,41,42,43,44,55,56,57,58,59,65,66,67,68,69,75,76,77,78,79,85,86,87,88,89,90,91,92,93,94],0,[-1]),
(5,[12,64],0,[-1]),
(5,[13,23,33,48],0,[-1]),
(5,[22,32,47],0,[-1]),
(5,[74],0,[-1]),
(5,[84],0,[-1]),
(5,[99],2,[0,1,2,3]),
(5,[99],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
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
(6,[2,3,54],0,[-1]),
(6,[4,14,24,34,49,50,51,52,53,60,61,62,63,70,71,72,73,80,81,82,83,95,96,97,98],0,[-1]),
(6,[5,6,7,8,9,15,16,17,18,19,25,26,27,28,29,35,36,37,38,39,40,41,42,43,44,55,56,57,58,59,65,66,67,68,69,75,76,77,78,79,85,86,87,88,89,90,91,92,93,94],0,[-1]),
(6,[12,64],0,[-1]),
(6,[13,23,33,48],0,[-1]),
(6,[22,32,47],0,[-1]),
(6,[74],0,[-1]),
(6,[84],0,[-1]),
(6,[99],0,[-1])]
private def checkedTasks : List CoverageTask := [(0,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 16 false).zipIdx.map Prod.swap),(6, (List.replicate 10 true).zipIdx.map Prod.swap),(7, (List.replicate 4 false).zipIdx.map Prod.swap),(8, (List.replicate 4 true).zipIdx.map Prod.swap),(9, (List.replicate 4 true).zipIdx.map Prod.swap),(10, (List.replicate 16 false).zipIdx.map Prod.swap),(11, (List.replicate 4 true).zipIdx.map Prod.swap),(12, (List.replicate 4 false).zipIdx.map Prod.swap),(13, (List.replicate 1 true).zipIdx.map Prod.swap),(14, (List.replicate 1 true).zipIdx.map Prod.swap),(15, (List.replicate 4 false).zipIdx.map Prod.swap),(16, (List.replicate 10 true).zipIdx.map Prod.swap),(17, (List.replicate 10 false).zipIdx.map Prod.swap),(18, (List.replicate 4 true).zipIdx.map Prod.swap),(19, (List.replicate 10 false).zipIdx.map Prod.swap),(20, (List.replicate 2 true).zipIdx.map Prod.swap),(21, (List.replicate 8 true).zipIdx.map Prod.swap)]),(1,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 16 false).zipIdx.map Prod.swap),(6, (List.replicate 10 true).zipIdx.map Prod.swap),(7, (List.replicate 4 false).zipIdx.map Prod.swap),(8, (List.replicate 4 true).zipIdx.map Prod.swap),(9, (List.replicate 4 true).zipIdx.map Prod.swap),(10, (List.replicate 16 false).zipIdx.map Prod.swap),(11, (List.replicate 4 true).zipIdx.map Prod.swap),(12, (List.replicate 25 false).zipIdx.map Prod.swap),(13, (List.replicate 10 true).zipIdx.map Prod.swap),(14, (List.replicate 10 false).zipIdx.map Prod.swap),(15, (List.replicate 10 true).zipIdx.map Prod.swap),(16, (List.replicate 10 true).zipIdx.map Prod.swap),(17, (List.replicate 10 false).zipIdx.map Prod.swap),(18, (List.replicate 2 true).zipIdx.map Prod.swap),(19, (List.replicate 20 false).zipIdx.map Prod.swap),(20, (List.replicate 2 true).zipIdx.map Prod.swap),(21, [false, true, false, false].zipIdx.map Prod.swap)]),(2,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 16 false).zipIdx.map Prod.swap),(6, (List.replicate 10 true).zipIdx.map Prod.swap),(7, (List.replicate 4 false).zipIdx.map Prod.swap),(8, (List.replicate 4 true).zipIdx.map Prod.swap),(9, (List.replicate 4 true).zipIdx.map Prod.swap),(10, (List.replicate 16 false).zipIdx.map Prod.swap),(11, (List.replicate 4 true).zipIdx.map Prod.swap),(12, (List.replicate 25 false).zipIdx.map Prod.swap),(13, (List.replicate 10 true).zipIdx.map Prod.swap),(14, (List.replicate 10 false).zipIdx.map Prod.swap),(15, (List.replicate 10 true).zipIdx.map Prod.swap),(16, (List.replicate 4 true).zipIdx.map Prod.swap),(17, (List.replicate 10 true).zipIdx.map Prod.swap),(18, (List.replicate 10 false).zipIdx.map Prod.swap),(19, (List.replicate 10 true).zipIdx.map Prod.swap),(20, (List.replicate 10 false).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 10 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 10 true).zipIdx.map Prod.swap),(27, (List.replicate 10 false).zipIdx.map Prod.swap),(28, (List.replicate 2 true).zipIdx.map Prod.swap),(29, (List.replicate 20 false).zipIdx.map Prod.swap),(30, [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false].zipIdx.map Prod.swap),(31, (List.replicate 1 false).zipIdx.map Prod.swap),(32, (List.replicate 2 true).zipIdx.map Prod.swap),(33, (List.replicate 4 true).zipIdx.map Prod.swap)]),(3,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 16 false).zipIdx.map Prod.swap),(6, (List.replicate 4 true).zipIdx.map Prod.swap),(7, (List.replicate 10 false).zipIdx.map Prod.swap),(8, (List.replicate 10 true).zipIdx.map Prod.swap),(9, (List.replicate 25 false).zipIdx.map Prod.swap),(10, (List.replicate 25 true).zipIdx.map Prod.swap),(11, (List.replicate 1 true).zipIdx.map Prod.swap),(12, (List.replicate 10 false).zipIdx.map Prod.swap),(13, (List.replicate 4 true).zipIdx.map Prod.swap),(14, (List.replicate 10 false).zipIdx.map Prod.swap),(15, (List.replicate 10 true).zipIdx.map Prod.swap),(16, (List.replicate 16 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 25 true).zipIdx.map Prod.swap),(19, (List.replicate 25 false).zipIdx.map Prod.swap),(20, (List.replicate 25 true).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 25 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 4 true).zipIdx.map Prod.swap),(27, (List.replicate 25 false).zipIdx.map Prod.swap),(28, (List.replicate 10 true).zipIdx.map Prod.swap),(29, (List.replicate 10 false).zipIdx.map Prod.swap),(30, (List.replicate 10 true).zipIdx.map Prod.swap),(31, (List.replicate 8 true).zipIdx.map Prod.swap),(32, (List.replicate 5 false).zipIdx.map Prod.swap),(33, (List.replicate 1 true).zipIdx.map Prod.swap),(34, (List.replicate 4 false).zipIdx.map Prod.swap),(35, (List.replicate 4 false).zipIdx.map Prod.swap),(36, (List.replicate 4 false).zipIdx.map Prod.swap),(37, (List.replicate 4 true).zipIdx.map Prod.swap),(38, (List.replicate 16 false).zipIdx.map Prod.swap),(39, (List.replicate 4 false).zipIdx.map Prod.swap),(40, (List.replicate 4 false).zipIdx.map Prod.swap),(41, (List.replicate 2 true).zipIdx.map Prod.swap),(42, [false, true, false, false].zipIdx.map Prod.swap)]),(4,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 16 false).zipIdx.map Prod.swap),(6, (List.replicate 4 true).zipIdx.map Prod.swap),(7, (List.replicate 10 false).zipIdx.map Prod.swap),(8, (List.replicate 10 true).zipIdx.map Prod.swap),(9, (List.replicate 25 false).zipIdx.map Prod.swap),(10, (List.replicate 25 true).zipIdx.map Prod.swap),(11, (List.replicate 1 true).zipIdx.map Prod.swap),(12, (List.replicate 10 false).zipIdx.map Prod.swap),(13, (List.replicate 4 true).zipIdx.map Prod.swap),(14, (List.replicate 10 false).zipIdx.map Prod.swap),(15, (List.replicate 10 true).zipIdx.map Prod.swap),(16, (List.replicate 16 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 25 true).zipIdx.map Prod.swap),(19, (List.replicate 25 false).zipIdx.map Prod.swap),(20, (List.replicate 25 true).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 25 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 4 true).zipIdx.map Prod.swap),(27, (List.replicate 25 false).zipIdx.map Prod.swap),(28, (List.replicate 10 true).zipIdx.map Prod.swap),(29, (List.replicate 10 false).zipIdx.map Prod.swap),(30, (List.replicate 10 true).zipIdx.map Prod.swap),(31, (List.replicate 4 true).zipIdx.map Prod.swap),(32, (List.replicate 10 true).zipIdx.map Prod.swap),(33, (List.replicate 10 false).zipIdx.map Prod.swap),(34, (List.replicate 10 true).zipIdx.map Prod.swap),(35, (List.replicate 10 false).zipIdx.map Prod.swap),(36, (List.replicate 4 true).zipIdx.map Prod.swap),(37, (List.replicate 10 false).zipIdx.map Prod.swap),(38, (List.replicate 10 true).zipIdx.map Prod.swap),(39, (List.replicate 10 false).zipIdx.map Prod.swap),(40, (List.replicate 10 true).zipIdx.map Prod.swap),(41, (List.replicate 8 true).zipIdx.map Prod.swap),(42, (List.replicate 5 false).zipIdx.map Prod.swap),(43, (List.replicate 1 true).zipIdx.map Prod.swap),(44, (List.replicate 4 false).zipIdx.map Prod.swap),(45, (List.replicate 4 false).zipIdx.map Prod.swap),(46, (List.replicate 4 false).zipIdx.map Prod.swap),(47, (List.replicate 4 true).zipIdx.map Prod.swap),(48, (List.replicate 16 false).zipIdx.map Prod.swap),(49, (List.replicate 4 false).zipIdx.map Prod.swap),(50, (List.replicate 4 false).zipIdx.map Prod.swap),(51, [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false].zipIdx.map Prod.swap),(52, (List.replicate 1 false).zipIdx.map Prod.swap),(53, (List.replicate 2 true).zipIdx.map Prod.swap),(54, (List.replicate 4 true).zipIdx.map Prod.swap)]),(5,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 16 false).zipIdx.map Prod.swap),(6, (List.replicate 4 true).zipIdx.map Prod.swap),(7, (List.replicate 10 false).zipIdx.map Prod.swap),(8, (List.replicate 10 true).zipIdx.map Prod.swap),(9, (List.replicate 25 false).zipIdx.map Prod.swap),(10, (List.replicate 25 true).zipIdx.map Prod.swap),(11, (List.replicate 10 true).zipIdx.map Prod.swap),(12, (List.replicate 16 false).zipIdx.map Prod.swap),(13, (List.replicate 4 true).zipIdx.map Prod.swap),(14, (List.replicate 4 true).zipIdx.map Prod.swap),(15, (List.replicate 4 false).zipIdx.map Prod.swap),(16, (List.replicate 16 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 25 true).zipIdx.map Prod.swap),(19, (List.replicate 25 false).zipIdx.map Prod.swap),(20, (List.replicate 25 true).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 25 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 4 true).zipIdx.map Prod.swap),(27, (List.replicate 25 false).zipIdx.map Prod.swap),(28, (List.replicate 10 true).zipIdx.map Prod.swap),(29, (List.replicate 10 false).zipIdx.map Prod.swap),(30, (List.replicate 10 true).zipIdx.map Prod.swap),(31, (List.replicate 8 true).zipIdx.map Prod.swap),(32, (List.replicate 5 false).zipIdx.map Prod.swap),(33, (List.replicate 2 true).zipIdx.map Prod.swap),(34, (List.replicate 20 false).zipIdx.map Prod.swap),(35, (List.replicate 20 false).zipIdx.map Prod.swap),(36, (List.replicate 8 false).zipIdx.map Prod.swap),(37, (List.replicate 4 true).zipIdx.map Prod.swap),(38, (List.replicate 16 false).zipIdx.map Prod.swap),(39, (List.replicate 4 false).zipIdx.map Prod.swap),(40, (List.replicate 4 false).zipIdx.map Prod.swap),(41, (List.replicate 2 true).zipIdx.map Prod.swap),(42, [false, true, false, false].zipIdx.map Prod.swap)]),(6,[(1, (List.replicate 10 true).zipIdx.map Prod.swap),(2, (List.replicate 4 false).zipIdx.map Prod.swap),(3, (List.replicate 4 true).zipIdx.map Prod.swap),(4, (List.replicate 4 true).zipIdx.map Prod.swap),(5, (List.replicate 16 false).zipIdx.map Prod.swap),(6, (List.replicate 4 true).zipIdx.map Prod.swap),(7, (List.replicate 10 false).zipIdx.map Prod.swap),(8, (List.replicate 10 true).zipIdx.map Prod.swap),(9, (List.replicate 25 false).zipIdx.map Prod.swap),(10, (List.replicate 25 true).zipIdx.map Prod.swap),(11, (List.replicate 10 true).zipIdx.map Prod.swap),(12, (List.replicate 16 false).zipIdx.map Prod.swap),(13, (List.replicate 4 true).zipIdx.map Prod.swap),(14, (List.replicate 4 true).zipIdx.map Prod.swap),(15, (List.replicate 4 false).zipIdx.map Prod.swap),(16, (List.replicate 16 true).zipIdx.map Prod.swap),(17, (List.replicate 25 false).zipIdx.map Prod.swap),(18, (List.replicate 25 true).zipIdx.map Prod.swap),(19, (List.replicate 25 false).zipIdx.map Prod.swap),(20, (List.replicate 25 true).zipIdx.map Prod.swap),(21, (List.replicate 4 true).zipIdx.map Prod.swap),(22, (List.replicate 10 false).zipIdx.map Prod.swap),(23, (List.replicate 10 true).zipIdx.map Prod.swap),(24, (List.replicate 25 false).zipIdx.map Prod.swap),(25, (List.replicate 10 true).zipIdx.map Prod.swap),(26, (List.replicate 4 true).zipIdx.map Prod.swap),(27, (List.replicate 25 false).zipIdx.map Prod.swap),(28, (List.replicate 10 true).zipIdx.map Prod.swap),(29, (List.replicate 10 false).zipIdx.map Prod.swap),(30, (List.replicate 10 true).zipIdx.map Prod.swap),(31, (List.replicate 4 true).zipIdx.map Prod.swap),(32, (List.replicate 10 true).zipIdx.map Prod.swap),(33, (List.replicate 10 false).zipIdx.map Prod.swap),(34, (List.replicate 10 true).zipIdx.map Prod.swap),(35, (List.replicate 10 false).zipIdx.map Prod.swap),(36, (List.replicate 4 true).zipIdx.map Prod.swap),(37, (List.replicate 10 false).zipIdx.map Prod.swap),(38, (List.replicate 10 true).zipIdx.map Prod.swap),(39, (List.replicate 10 false).zipIdx.map Prod.swap),(40, (List.replicate 10 true).zipIdx.map Prod.swap),(41, (List.replicate 8 true).zipIdx.map Prod.swap),(42, (List.replicate 5 false).zipIdx.map Prod.swap),(43, (List.replicate 2 true).zipIdx.map Prod.swap),(44, (List.replicate 20 false).zipIdx.map Prod.swap),(45, (List.replicate 20 false).zipIdx.map Prod.swap),(46, (List.replicate 8 false).zipIdx.map Prod.swap),(47, (List.replicate 4 true).zipIdx.map Prod.swap),(48, (List.replicate 16 false).zipIdx.map Prod.swap),(49, (List.replicate 4 false).zipIdx.map Prod.swap),(50, (List.replicate 4 false).zipIdx.map Prod.swap),(51, [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false].zipIdx.map Prod.swap),(52, (List.replicate 1 false).zipIdx.map Prod.swap),(53, (List.replicate 2 true).zipIdx.map Prod.swap),(54, (List.replicate 4 true).zipIdx.map Prod.swap)])]
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
private abbrev specAt2 (pi goal : ℕ) : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 2) pi))[goal-1]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private abbrev cSpec2_0_1 := specAt2 0 1
private theorem cFlags2_0_1 : automaticFlags (trunkCatalog.states 2).context cSpec2_0_1 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_2 coordinateInput2_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_2 hCoordinate2_1]
  decide +kernel
private abbrev cSpec2_0_2 := specAt2 0 2
private theorem cFlags2_0_2 : automaticFlags (trunkCatalog.states 2).context cSpec2_0_2 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_4 coordinateInput2_5 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_4 hCoordinate2_5]
  decide +kernel
private abbrev cSpec2_0_3 := specAt2 0 3
private theorem cFlags2_0_3 : automaticFlags (trunkCatalog.states 2).context cSpec2_0_3 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_6 coordinateInput2_7 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_6 hCoordinate2_7]
  decide +kernel
private abbrev cSpec2_0_4 := specAt2 0 4
private theorem cFlags2_0_4 : automaticFlags (trunkCatalog.states 2).context cSpec2_0_4 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_8 coordinateInput2_9 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_8 hCoordinate2_9]
  decide +kernel
private abbrev cSpec2_0_5 := specAt2 0 5
private theorem cFlags2_0_5 : automaticFlags (trunkCatalog.states 2).context cSpec2_0_5 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_10 coordinateInput2_11 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_10 hCoordinate2_11]
  decide +kernel
private abbrev cSpec2_0_6 := specAt2 0 6
private theorem cFlags2_0_6 : automaticFlags (trunkCatalog.states 2).context cSpec2_0_6 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_0 coordinateInput2_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_0 hCoordinate2_3]
  decide +kernel
private abbrev cSpec2_0_7 := specAt2 0 7
private theorem cFlags2_0_7 : automaticFlags (trunkCatalog.states 2).context cSpec2_0_7 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_12 coordinateInput2_13 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_12 hCoordinate2_13]
  decide +kernel
private abbrev cSpec2_0_8 := specAt2 0 8
private theorem cFlags2_0_8 : automaticFlags (trunkCatalog.states 2).context cSpec2_0_8 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_14 coordinateInput2_15 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_14 hCoordinate2_15]
  decide +kernel
private abbrev cSpec2_0_9 := specAt2 0 9
private theorem cFlags2_0_9 : automaticFlags (trunkCatalog.states 2).context cSpec2_0_9 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_16 coordinateInput2_17 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_16 hCoordinate2_17]
  decide +kernel
private abbrev cSpec2_0_10 := specAt2 0 10
private theorem cFlags2_0_10 : automaticFlags (trunkCatalog.states 2).context cSpec2_0_10 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_18 coordinateInput2_19 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_18 hCoordinate2_19]
  decide +kernel
private abbrev cSpec2_0_11 := specAt2 0 11
private theorem cFlags2_0_11 : automaticFlags (trunkCatalog.states 2).context cSpec2_0_11 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_20 coordinateInput2_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_20 hCoordinate2_21]
  decide +kernel
private abbrev cSpec2_0_12 := specAt2 0 12
private theorem cFlags2_0_12 : automaticFlags (trunkCatalog.states 2).context cSpec2_0_12 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_22 coordinateInput2_23 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_22 hCoordinate2_23]
  decide +kernel
private abbrev cSpec2_0_13 := specAt2 0 13
private theorem cFlags2_0_13 : automaticFlags (trunkCatalog.states 2).context cSpec2_0_13 = (List.replicate 1 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_24 coordinateInput2_25 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_24 hCoordinate2_25]
  decide +kernel
private abbrev cSpec2_0_14 := specAt2 0 14
private theorem cFlags2_0_14 : automaticFlags (trunkCatalog.states 2).context cSpec2_0_14 = (List.replicate 1 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_26 coordinateInput2_27 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_26 hCoordinate2_27]
  decide +kernel
private abbrev cSpec2_0_15 := specAt2 0 15
private theorem cFlags2_0_15 : automaticFlags (trunkCatalog.states 2).context cSpec2_0_15 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_28 coordinateInput2_29 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_28 hCoordinate2_29]
  decide +kernel
private abbrev cSpec2_0_16 := specAt2 0 16
private theorem cFlags2_0_16 : automaticFlags (trunkCatalog.states 2).context cSpec2_0_16 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_2 coordinateInput2_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_2 hCoordinate2_3]
  decide +kernel
private abbrev cSpec2_0_17 := specAt2 0 17
private theorem cFlags2_0_17 : automaticFlags (trunkCatalog.states 2).context cSpec2_0_17 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_0 coordinateInput2_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_0 hCoordinate2_1]
  decide +kernel
private abbrev cSpec2_0_18 := specAt2 0 18
private theorem cFlags2_0_18 : automaticFlags (trunkCatalog.states 2).context cSpec2_0_18 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_0 coordinateInput2_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_0 hCoordinate2_21]
  decide +kernel
private abbrev cSpec2_0_19 := specAt2 0 19
private theorem cFlags2_0_19 : automaticFlags (trunkCatalog.states 2).context cSpec2_0_19 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_20 coordinateInput2_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_20 hCoordinate2_3]
  decide +kernel
private abbrev cSpec2_0_20 := specAt2 0 20
private theorem cFlags2_0_20 : automaticFlags (trunkCatalog.states 2).context cSpec2_0_20 = (List.replicate 2 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_2 coordinateInput2_30 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_2 hCoordinate2_30]
  decide +kernel
private abbrev cSpec2_0_21 := specAt2 0 21
private theorem cFlags2_0_21 : automaticFlags (trunkCatalog.states 2).context cSpec2_0_21 = (List.replicate 8 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_31 coordinateInput2_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_31 hCoordinate2_21]
  decide +kernel
private abbrev cSpec2_1_1 := specAt2 1 1
private theorem cFlags2_1_1 : automaticFlags (trunkCatalog.states 2).context cSpec2_1_1 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_1

private abbrev cSpec2_1_2 := specAt2 1 2
private theorem cFlags2_1_2 : automaticFlags (trunkCatalog.states 2).context cSpec2_1_2 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec2_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_2

private abbrev cSpec2_1_3 := specAt2 1 3
private theorem cFlags2_1_3 : automaticFlags (trunkCatalog.states 2).context cSpec2_1_3 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_3

private abbrev cSpec2_1_4 := specAt2 1 4
private theorem cFlags2_1_4 : automaticFlags (trunkCatalog.states 2).context cSpec2_1_4 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_4

private abbrev cSpec2_1_5 := specAt2 1 5
private theorem cFlags2_1_5 : automaticFlags (trunkCatalog.states 2).context cSpec2_1_5 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec2_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_5

private abbrev cSpec2_1_6 := specAt2 1 6
private theorem cFlags2_1_6 : automaticFlags (trunkCatalog.states 2).context cSpec2_1_6 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_6

private abbrev cSpec2_1_7 := specAt2 1 7
private theorem cFlags2_1_7 : automaticFlags (trunkCatalog.states 2).context cSpec2_1_7 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec2_0_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_7

private abbrev cSpec2_1_8 := specAt2 1 8
private theorem cFlags2_1_8 : automaticFlags (trunkCatalog.states 2).context cSpec2_1_8 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_8

private abbrev cSpec2_1_9 := specAt2 1 9
private theorem cFlags2_1_9 : automaticFlags (trunkCatalog.states 2).context cSpec2_1_9 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_9

private abbrev cSpec2_1_10 := specAt2 1 10
private theorem cFlags2_1_10 : automaticFlags (trunkCatalog.states 2).context cSpec2_1_10 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec2_0_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_10

private abbrev cSpec2_1_11 := specAt2 1 11
private theorem cFlags2_1_11 : automaticFlags (trunkCatalog.states 2).context cSpec2_1_11 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_32 coordinateInput2_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_32 hCoordinate2_33]
  decide +kernel
private abbrev cSpec2_1_12 := specAt2 1 12
private theorem cFlags2_1_12 : automaticFlags (trunkCatalog.states 2).context cSpec2_1_12 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_34 coordinateInput2_35 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_34 hCoordinate2_35]
  decide +kernel
private abbrev cSpec2_1_13 := specAt2 1 13
private theorem cFlags2_1_13 : automaticFlags (trunkCatalog.states 2).context cSpec2_1_13 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_36 coordinateInput2_37 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_36 hCoordinate2_37]
  decide +kernel
private abbrev cSpec2_1_14 := specAt2 1 14
private theorem cFlags2_1_14 : automaticFlags (trunkCatalog.states 2).context cSpec2_1_14 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_38 coordinateInput2_39 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_38 hCoordinate2_39]
  decide +kernel
private abbrev cSpec2_1_15 := specAt2 1 15
private theorem cFlags2_1_15 : automaticFlags (trunkCatalog.states 2).context cSpec2_1_15 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_40 coordinateInput2_41 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_40 hCoordinate2_41]
  decide +kernel
private abbrev cSpec2_1_16 := specAt2 1 16
private theorem cFlags2_1_16 : automaticFlags (trunkCatalog.states 2).context cSpec2_1_16 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_16

private abbrev cSpec2_1_17 := specAt2 1 17
private theorem cFlags2_1_17 : automaticFlags (trunkCatalog.states 2).context cSpec2_1_17 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_0_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_17

private abbrev cSpec2_1_18 := specAt2 1 18
private theorem cFlags2_1_18 : automaticFlags (trunkCatalog.states 2).context cSpec2_1_18 = (List.replicate 2 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_0 coordinateInput2_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_0 hCoordinate2_33]
  decide +kernel
private abbrev cSpec2_1_19 := specAt2 1 19
private theorem cFlags2_1_19 : automaticFlags (trunkCatalog.states 2).context cSpec2_1_19 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_32 coordinateInput2_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_32 hCoordinate2_3]
  decide +kernel
private abbrev cSpec2_1_20 := specAt2 1 20
private theorem cFlags2_1_20 : automaticFlags (trunkCatalog.states 2).context cSpec2_1_20 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_20

private abbrev cSpec2_1_21 := specAt2 1 21
private theorem cFlags2_1_21 : automaticFlags (trunkCatalog.states 2).context cSpec2_1_21 = [false, true, false, false] := by
  rw [automaticFlags_cached _ _ coordinateInput2_31 coordinateInput2_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_31 hCoordinate2_33]
  decide +kernel
private abbrev cSpec2_2_1 := specAt2 2 1
private theorem cFlags2_2_1 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_1 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_1

private abbrev cSpec2_2_2 := specAt2 2 2
private theorem cFlags2_2_2 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_2 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec2_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_2

private abbrev cSpec2_2_3 := specAt2 2 3
private theorem cFlags2_2_3 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_3 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_3

private abbrev cSpec2_2_4 := specAt2 2 4
private theorem cFlags2_2_4 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_4 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_4

private abbrev cSpec2_2_5 := specAt2 2 5
private theorem cFlags2_2_5 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_5 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec2_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_5

private abbrev cSpec2_2_6 := specAt2 2 6
private theorem cFlags2_2_6 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_6 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_6

private abbrev cSpec2_2_7 := specAt2 2 7
private theorem cFlags2_2_7 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_7 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec2_0_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_7

private abbrev cSpec2_2_8 := specAt2 2 8
private theorem cFlags2_2_8 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_8 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_8

private abbrev cSpec2_2_9 := specAt2 2 9
private theorem cFlags2_2_9 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_9 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_9

private abbrev cSpec2_2_10 := specAt2 2 10
private theorem cFlags2_2_10 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_10 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec2_0_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_10

private abbrev cSpec2_2_11 := specAt2 2 11
private theorem cFlags2_2_11 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_11 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_11

private abbrev cSpec2_2_12 := specAt2 2 12
private theorem cFlags2_2_12 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_12 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec2_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_12

private abbrev cSpec2_2_13 := specAt2 2 13
private theorem cFlags2_2_13 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_13 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_13

private abbrev cSpec2_2_14 := specAt2 2 14
private theorem cFlags2_2_14 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_14 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_14

private abbrev cSpec2_2_15 := specAt2 2 15
private theorem cFlags2_2_15 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_15 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_15

private abbrev cSpec2_2_16 := specAt2 2 16
private theorem cFlags2_2_16 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_16 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_42 coordinateInput2_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_42 hCoordinate2_43]
  decide +kernel
private abbrev cSpec2_2_17 := specAt2 2 17
private theorem cFlags2_2_17 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_17 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_44 coordinateInput2_45 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_44 hCoordinate2_45]
  decide +kernel
private abbrev cSpec2_2_18 := specAt2 2 18
private theorem cFlags2_2_18 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_18 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_46 coordinateInput2_47 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_46 hCoordinate2_47]
  decide +kernel
private abbrev cSpec2_2_19 := specAt2 2 19
private theorem cFlags2_2_19 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_19 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_48 coordinateInput2_49 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_48 hCoordinate2_49]
  decide +kernel
private abbrev cSpec2_2_20 := specAt2 2 20
private theorem cFlags2_2_20 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_20 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_50 coordinateInput2_51 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_50 hCoordinate2_51]
  decide +kernel
private abbrev cSpec2_2_21 := specAt2 2 21
private theorem cFlags2_2_21 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_21 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_52 coordinateInput2_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_52 hCoordinate2_53]
  decide +kernel
private abbrev cSpec2_2_22 := specAt2 2 22
private theorem cFlags2_2_22 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_22 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_54 coordinateInput2_55 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_54 hCoordinate2_55]
  decide +kernel
private abbrev cSpec2_2_23 := specAt2 2 23
private theorem cFlags2_2_23 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_23 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_56 coordinateInput2_57 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_56 hCoordinate2_57]
  decide +kernel
private abbrev cSpec2_2_24 := specAt2 2 24
private theorem cFlags2_2_24 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_24 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_58 coordinateInput2_59 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_58 hCoordinate2_59]
  decide +kernel
private abbrev cSpec2_2_25 := specAt2 2 25
private theorem cFlags2_2_25 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_25 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_60 coordinateInput2_61 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_60 hCoordinate2_61]
  decide +kernel
private abbrev cSpec2_2_26 := specAt2 2 26
private theorem cFlags2_2_26 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_26 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_16

private abbrev cSpec2_2_27 := specAt2 2 27
private theorem cFlags2_2_27 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_27 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_0_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_17

private abbrev cSpec2_2_28 := specAt2 2 28
private theorem cFlags2_2_28 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_28 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec2_1_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_18

private abbrev cSpec2_2_29 := specAt2 2 29
private theorem cFlags2_2_29 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_29 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec2_1_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_19

private abbrev cSpec2_2_30 := specAt2 2 30
private theorem cFlags2_2_30 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_30 = [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false] := by
  rw [automaticFlags_cached _ _ coordinateInput2_32 coordinateInput2_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_32 hCoordinate2_43]
  decide +kernel
private abbrev cSpec2_2_31 := specAt2 2 31
private theorem cFlags2_2_31 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_31 = (List.replicate 1 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_42 coordinateInput2_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_42 hCoordinate2_33]
  decide +kernel
private abbrev cSpec2_2_32 := specAt2 2 32
private theorem cFlags2_2_32 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_32 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_20

private abbrev cSpec2_2_33 := specAt2 2 33
private theorem cFlags2_2_33 : automaticFlags (trunkCatalog.states 2).context cSpec2_2_33 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_31 coordinateInput2_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_31 hCoordinate2_53]
  decide +kernel
private abbrev cSpec2_3_1 := specAt2 3 1
private theorem cFlags2_3_1 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_1 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_1

private abbrev cSpec2_3_2 := specAt2 3 2
private theorem cFlags2_3_2 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_2 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec2_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_2

private abbrev cSpec2_3_3 := specAt2 3 3
private theorem cFlags2_3_3 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_3 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_3

private abbrev cSpec2_3_4 := specAt2 3 4
private theorem cFlags2_3_4 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_4 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_4

private abbrev cSpec2_3_5 := specAt2 3 5
private theorem cFlags2_3_5 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_5 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec2_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_5

private abbrev cSpec2_3_6 := specAt2 3 6
private theorem cFlags2_3_6 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_6 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_62 coordinateInput2_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_62 hCoordinate2_63]
  decide +kernel
private abbrev cSpec2_3_7 := specAt2 3 7
private theorem cFlags2_3_7 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_7 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_64 coordinateInput2_65 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_64 hCoordinate2_65]
  decide +kernel
private abbrev cSpec2_3_8 := specAt2 3 8
private theorem cFlags2_3_8 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_8 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_66 coordinateInput2_67 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_66 hCoordinate2_67]
  decide +kernel
private abbrev cSpec2_3_9 := specAt2 3 9
private theorem cFlags2_3_9 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_9 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_68 coordinateInput2_69 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_68 hCoordinate2_69]
  decide +kernel
private abbrev cSpec2_3_10 := specAt2 3 10
private theorem cFlags2_3_10 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_10 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_70 coordinateInput2_71 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_70 hCoordinate2_71]
  decide +kernel
private abbrev cSpec2_3_11 := specAt2 3 11
private theorem cFlags2_3_11 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_11 = (List.replicate 1 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_72 coordinateInput2_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_72 hCoordinate2_73]
  decide +kernel
private abbrev cSpec2_3_12 := specAt2 3 12
private theorem cFlags2_3_12 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_12 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_74 coordinateInput2_75 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_74 hCoordinate2_75]
  decide +kernel
private abbrev cSpec2_3_13 := specAt2 3 13
private theorem cFlags2_3_13 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_13 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_76 coordinateInput2_77 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_76 hCoordinate2_77]
  decide +kernel
private abbrev cSpec2_3_14 := specAt2 3 14
private theorem cFlags2_3_14 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_14 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_78 coordinateInput2_79 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_78 hCoordinate2_79]
  decide +kernel
private abbrev cSpec2_3_15 := specAt2 3 15
private theorem cFlags2_3_15 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_15 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_80 coordinateInput2_81 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_80 hCoordinate2_81]
  decide +kernel
private abbrev cSpec2_3_16 := specAt2 3 16
private theorem cFlags2_3_16 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_16 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_82 coordinateInput2_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_82 hCoordinate2_83]
  decide +kernel
private abbrev cSpec2_3_17 := specAt2 3 17
private theorem cFlags2_3_17 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_17 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_84 coordinateInput2_85 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_84 hCoordinate2_85]
  decide +kernel
private abbrev cSpec2_3_18 := specAt2 3 18
private theorem cFlags2_3_18 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_18 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_86 coordinateInput2_87 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_86 hCoordinate2_87]
  decide +kernel
private abbrev cSpec2_3_19 := specAt2 3 19
private theorem cFlags2_3_19 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_19 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_88 coordinateInput2_89 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_88 hCoordinate2_89]
  decide +kernel
private abbrev cSpec2_3_20 := specAt2 3 20
private theorem cFlags2_3_20 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_20 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_90 coordinateInput2_91 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_90 hCoordinate2_91]
  decide +kernel
private abbrev cSpec2_3_21 := specAt2 3 21
private theorem cFlags2_3_21 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_21 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_92 coordinateInput2_93 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_92 hCoordinate2_93]
  decide +kernel
private abbrev cSpec2_3_22 := specAt2 3 22
private theorem cFlags2_3_22 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_22 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_94 coordinateInput2_95 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_94 hCoordinate2_95]
  decide +kernel
private abbrev cSpec2_3_23 := specAt2 3 23
private theorem cFlags2_3_23 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_23 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_96 coordinateInput2_97 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_96 hCoordinate2_97]
  decide +kernel
private abbrev cSpec2_3_24 := specAt2 3 24
private theorem cFlags2_3_24 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_24 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_98 coordinateInput2_99 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_98 hCoordinate2_99]
  decide +kernel
private abbrev cSpec2_3_25 := specAt2 3 25
private theorem cFlags2_3_25 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_25 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_100 coordinateInput2_101 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_100 hCoordinate2_101]
  decide +kernel
private abbrev cSpec2_3_26 := specAt2 3 26
private theorem cFlags2_3_26 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_11

private abbrev cSpec2_3_27 := specAt2 3 27
private theorem cFlags2_3_27 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec2_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_12

private abbrev cSpec2_3_28 := specAt2 3 28
private theorem cFlags2_3_28 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_13

private abbrev cSpec2_3_29 := specAt2 3 29
private theorem cFlags2_3_29 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_14

private abbrev cSpec2_3_30 := specAt2 3 30
private theorem cFlags2_3_30 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_15

private abbrev cSpec2_3_31 := specAt2 3 31
private theorem cFlags2_3_31 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_31 = (List.replicate 8 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_2 coordinateInput2_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_2 hCoordinate2_63]
  decide +kernel
private abbrev cSpec2_3_32 := specAt2 3 32
private theorem cFlags2_3_32 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_32 = (List.replicate 5 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_62 coordinateInput2_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_62 hCoordinate2_1]
  decide +kernel
private abbrev cSpec2_3_33 := specAt2 3 33
private theorem cFlags2_3_33 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_33 = (List.replicate 1 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_62 coordinateInput2_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_62 hCoordinate2_73]
  decide +kernel
private abbrev cSpec2_3_34 := specAt2 3 34
private theorem cFlags2_3_34 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_34 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_72 coordinateInput2_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_72 hCoordinate2_63]
  decide +kernel
private abbrev cSpec2_3_35 := specAt2 3 35
private theorem cFlags2_3_35 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_35 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_72 coordinateInput2_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_72 hCoordinate2_83]
  decide +kernel
private abbrev cSpec2_3_36 := specAt2 3 36
private theorem cFlags2_3_36 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_36 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_82 coordinateInput2_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_82 hCoordinate2_73]
  decide +kernel
private abbrev cSpec2_3_37 := specAt2 3 37
private theorem cFlags2_3_37 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_37 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_82 coordinateInput2_93 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_82 hCoordinate2_93]
  decide +kernel
private abbrev cSpec2_3_38 := specAt2 3 38
private theorem cFlags2_3_38 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_38 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_92 coordinateInput2_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_92 hCoordinate2_83]
  decide +kernel
private abbrev cSpec2_3_39 := specAt2 3 39
private theorem cFlags2_3_39 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_39 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_92 coordinateInput2_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_92 hCoordinate2_33]
  decide +kernel
private abbrev cSpec2_3_40 := specAt2 3 40
private theorem cFlags2_3_40 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_40 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_32 coordinateInput2_93 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_32 hCoordinate2_93]
  decide +kernel
private abbrev cSpec2_3_41 := specAt2 3 41
private theorem cFlags2_3_41 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_41 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_20

private abbrev cSpec2_3_42 := specAt2 3 42
private theorem cFlags2_3_42 : automaticFlags (trunkCatalog.states 2).context cSpec2_3_42 = [false, true, false, false] := by
  exact (automaticFlags_same _ _ cSpec2_1_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_21

private abbrev cSpec2_4_1 := specAt2 4 1
private theorem cFlags2_4_1 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_1 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_1

private abbrev cSpec2_4_2 := specAt2 4 2
private theorem cFlags2_4_2 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_2 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec2_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_2

private abbrev cSpec2_4_3 := specAt2 4 3
private theorem cFlags2_4_3 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_3 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_3

private abbrev cSpec2_4_4 := specAt2 4 4
private theorem cFlags2_4_4 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_4 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_4

private abbrev cSpec2_4_5 := specAt2 4 5
private theorem cFlags2_4_5 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_5 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec2_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_5

private abbrev cSpec2_4_6 := specAt2 4 6
private theorem cFlags2_4_6 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_6 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_6

private abbrev cSpec2_4_7 := specAt2 4 7
private theorem cFlags2_4_7 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_7 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_7

private abbrev cSpec2_4_8 := specAt2 4 8
private theorem cFlags2_4_8 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_8 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_8

private abbrev cSpec2_4_9 := specAt2 4 9
private theorem cFlags2_4_9 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_9 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_9

private abbrev cSpec2_4_10 := specAt2 4 10
private theorem cFlags2_4_10 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_10 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_10

private abbrev cSpec2_4_11 := specAt2 4 11
private theorem cFlags2_4_11 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_11 = (List.replicate 1 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_11

private abbrev cSpec2_4_12 := specAt2 4 12
private theorem cFlags2_4_12 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_12 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_12

private abbrev cSpec2_4_13 := specAt2 4 13
private theorem cFlags2_4_13 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_13 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_13

private abbrev cSpec2_4_14 := specAt2 4 14
private theorem cFlags2_4_14 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_14 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_14

private abbrev cSpec2_4_15 := specAt2 4 15
private theorem cFlags2_4_15 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_15 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_15

private abbrev cSpec2_4_16 := specAt2 4 16
private theorem cFlags2_4_16 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_16 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_16

private abbrev cSpec2_4_17 := specAt2 4 17
private theorem cFlags2_4_17 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_17

private abbrev cSpec2_4_18 := specAt2 4 18
private theorem cFlags2_4_18 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_18 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_18

private abbrev cSpec2_4_19 := specAt2 4 19
private theorem cFlags2_4_19 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_19 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_19

private abbrev cSpec2_4_20 := specAt2 4 20
private theorem cFlags2_4_20 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_20 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_20

private abbrev cSpec2_4_21 := specAt2 4 21
private theorem cFlags2_4_21 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_21 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_21

private abbrev cSpec2_4_22 := specAt2 4 22
private theorem cFlags2_4_22 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_22 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_22

private abbrev cSpec2_4_23 := specAt2 4 23
private theorem cFlags2_4_23 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_23 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_23

private abbrev cSpec2_4_24 := specAt2 4 24
private theorem cFlags2_4_24 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_24 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_24

private abbrev cSpec2_4_25 := specAt2 4 25
private theorem cFlags2_4_25 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_25 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_25

private abbrev cSpec2_4_26 := specAt2 4 26
private theorem cFlags2_4_26 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_11

private abbrev cSpec2_4_27 := specAt2 4 27
private theorem cFlags2_4_27 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec2_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_12

private abbrev cSpec2_4_28 := specAt2 4 28
private theorem cFlags2_4_28 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_13

private abbrev cSpec2_4_29 := specAt2 4 29
private theorem cFlags2_4_29 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_14

private abbrev cSpec2_4_30 := specAt2 4 30
private theorem cFlags2_4_30 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_15

private abbrev cSpec2_4_31 := specAt2 4 31
private theorem cFlags2_4_31 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_31 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_2_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_16

private abbrev cSpec2_4_32 := specAt2 4 32
private theorem cFlags2_4_32 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_32 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_2_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_17

private abbrev cSpec2_4_33 := specAt2 4 33
private theorem cFlags2_4_33 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_33 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_2_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_18

private abbrev cSpec2_4_34 := specAt2 4 34
private theorem cFlags2_4_34 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_34 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_2_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_19

private abbrev cSpec2_4_35 := specAt2 4 35
private theorem cFlags2_4_35 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_35 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_2_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_20

private abbrev cSpec2_4_36 := specAt2 4 36
private theorem cFlags2_4_36 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_36 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_2_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_21

private abbrev cSpec2_4_37 := specAt2 4 37
private theorem cFlags2_4_37 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_37 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_2_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_22

private abbrev cSpec2_4_38 := specAt2 4 38
private theorem cFlags2_4_38 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_38 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_2_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_23

private abbrev cSpec2_4_39 := specAt2 4 39
private theorem cFlags2_4_39 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_39 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_2_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_24

private abbrev cSpec2_4_40 := specAt2 4 40
private theorem cFlags2_4_40 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_40 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_2_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_25

private abbrev cSpec2_4_41 := specAt2 4 41
private theorem cFlags2_4_41 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_41 = (List.replicate 8 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_31

private abbrev cSpec2_4_42 := specAt2 4 42
private theorem cFlags2_4_42 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_42 = (List.replicate 5 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_32

private abbrev cSpec2_4_43 := specAt2 4 43
private theorem cFlags2_4_43 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_43 = (List.replicate 1 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_33 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_33

private abbrev cSpec2_4_44 := specAt2 4 44
private theorem cFlags2_4_44 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_44 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_34 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_34

private abbrev cSpec2_4_45 := specAt2 4 45
private theorem cFlags2_4_45 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_45 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_35 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_35

private abbrev cSpec2_4_46 := specAt2 4 46
private theorem cFlags2_4_46 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_46 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_36 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_36

private abbrev cSpec2_4_47 := specAt2 4 47
private theorem cFlags2_4_47 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_47 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_37 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_37

private abbrev cSpec2_4_48 := specAt2 4 48
private theorem cFlags2_4_48 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_48 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_38 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_38

private abbrev cSpec2_4_49 := specAt2 4 49
private theorem cFlags2_4_49 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_49 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_39 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_39

private abbrev cSpec2_4_50 := specAt2 4 50
private theorem cFlags2_4_50 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_50 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_40 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_40

private abbrev cSpec2_4_51 := specAt2 4 51
private theorem cFlags2_4_51 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_51 = [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false] := by
  exact (automaticFlags_same _ _ cSpec2_2_30 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_30

private abbrev cSpec2_4_52 := specAt2 4 52
private theorem cFlags2_4_52 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_52 = (List.replicate 1 false) := by
  exact (automaticFlags_same _ _ cSpec2_2_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_31

private abbrev cSpec2_4_53 := specAt2 4 53
private theorem cFlags2_4_53 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_53 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_20

private abbrev cSpec2_4_54 := specAt2 4 54
private theorem cFlags2_4_54 : automaticFlags (trunkCatalog.states 2).context cSpec2_4_54 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_2_33 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_33

private abbrev cSpec2_5_1 := specAt2 5 1
private theorem cFlags2_5_1 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_1 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_1

private abbrev cSpec2_5_2 := specAt2 5 2
private theorem cFlags2_5_2 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_2 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec2_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_2

private abbrev cSpec2_5_3 := specAt2 5 3
private theorem cFlags2_5_3 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_3 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_3

private abbrev cSpec2_5_4 := specAt2 5 4
private theorem cFlags2_5_4 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_4 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_4

private abbrev cSpec2_5_5 := specAt2 5 5
private theorem cFlags2_5_5 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_5 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec2_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_5

private abbrev cSpec2_5_6 := specAt2 5 6
private theorem cFlags2_5_6 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_6 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_6

private abbrev cSpec2_5_7 := specAt2 5 7
private theorem cFlags2_5_7 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_7 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_7

private abbrev cSpec2_5_8 := specAt2 5 8
private theorem cFlags2_5_8 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_8 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_8

private abbrev cSpec2_5_9 := specAt2 5 9
private theorem cFlags2_5_9 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_9 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_9

private abbrev cSpec2_5_10 := specAt2 5 10
private theorem cFlags2_5_10 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_10 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_10

private abbrev cSpec2_5_11 := specAt2 5 11
private theorem cFlags2_5_11 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_11 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_102 coordinateInput2_103 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_102 hCoordinate2_103]
  decide +kernel
private abbrev cSpec2_5_12 := specAt2 5 12
private theorem cFlags2_5_12 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_12 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_104 coordinateInput2_105 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_104 hCoordinate2_105]
  decide +kernel
private abbrev cSpec2_5_13 := specAt2 5 13
private theorem cFlags2_5_13 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_13 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_106 coordinateInput2_107 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_106 hCoordinate2_107]
  decide +kernel
private abbrev cSpec2_5_14 := specAt2 5 14
private theorem cFlags2_5_14 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_14 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_108 coordinateInput2_109 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_108 hCoordinate2_109]
  decide +kernel
private abbrev cSpec2_5_15 := specAt2 5 15
private theorem cFlags2_5_15 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_15 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_110 coordinateInput2_111 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_110 hCoordinate2_111]
  decide +kernel
private abbrev cSpec2_5_16 := specAt2 5 16
private theorem cFlags2_5_16 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_16 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_16

private abbrev cSpec2_5_17 := specAt2 5 17
private theorem cFlags2_5_17 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_17

private abbrev cSpec2_5_18 := specAt2 5 18
private theorem cFlags2_5_18 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_18 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_18

private abbrev cSpec2_5_19 := specAt2 5 19
private theorem cFlags2_5_19 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_19 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_19

private abbrev cSpec2_5_20 := specAt2 5 20
private theorem cFlags2_5_20 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_20 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_20

private abbrev cSpec2_5_21 := specAt2 5 21
private theorem cFlags2_5_21 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_21 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_21

private abbrev cSpec2_5_22 := specAt2 5 22
private theorem cFlags2_5_22 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_22 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_22

private abbrev cSpec2_5_23 := specAt2 5 23
private theorem cFlags2_5_23 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_23 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_23

private abbrev cSpec2_5_24 := specAt2 5 24
private theorem cFlags2_5_24 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_24 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_24

private abbrev cSpec2_5_25 := specAt2 5 25
private theorem cFlags2_5_25 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_25 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_25

private abbrev cSpec2_5_26 := specAt2 5 26
private theorem cFlags2_5_26 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_11

private abbrev cSpec2_5_27 := specAt2 5 27
private theorem cFlags2_5_27 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec2_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_12

private abbrev cSpec2_5_28 := specAt2 5 28
private theorem cFlags2_5_28 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_13

private abbrev cSpec2_5_29 := specAt2 5 29
private theorem cFlags2_5_29 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_14

private abbrev cSpec2_5_30 := specAt2 5 30
private theorem cFlags2_5_30 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_15

private abbrev cSpec2_5_31 := specAt2 5 31
private theorem cFlags2_5_31 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_31 = (List.replicate 8 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_31

private abbrev cSpec2_5_32 := specAt2 5 32
private theorem cFlags2_5_32 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_32 = (List.replicate 5 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_32

private abbrev cSpec2_5_33 := specAt2 5 33
private theorem cFlags2_5_33 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_33 = (List.replicate 2 true) := by
  rw [automaticFlags_cached _ _ coordinateInput2_62 coordinateInput2_103 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_62 hCoordinate2_103]
  decide +kernel
private abbrev cSpec2_5_34 := specAt2 5 34
private theorem cFlags2_5_34 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_34 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_102 coordinateInput2_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_102 hCoordinate2_63]
  decide +kernel
private abbrev cSpec2_5_35 := specAt2 5 35
private theorem cFlags2_5_35 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_35 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_102 coordinateInput2_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_102 hCoordinate2_83]
  decide +kernel
private abbrev cSpec2_5_36 := specAt2 5 36
private theorem cFlags2_5_36 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_36 = (List.replicate 8 false) := by
  rw [automaticFlags_cached _ _ coordinateInput2_82 coordinateInput2_103 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate2_82 hCoordinate2_103]
  decide +kernel
private abbrev cSpec2_5_37 := specAt2 5 37
private theorem cFlags2_5_37 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_37 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_37 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_37

private abbrev cSpec2_5_38 := specAt2 5 38
private theorem cFlags2_5_38 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_38 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_38 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_38

private abbrev cSpec2_5_39 := specAt2 5 39
private theorem cFlags2_5_39 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_39 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_39 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_39

private abbrev cSpec2_5_40 := specAt2 5 40
private theorem cFlags2_5_40 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_40 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_40 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_40

private abbrev cSpec2_5_41 := specAt2 5 41
private theorem cFlags2_5_41 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_41 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_20

private abbrev cSpec2_5_42 := specAt2 5 42
private theorem cFlags2_5_42 : automaticFlags (trunkCatalog.states 2).context cSpec2_5_42 = [false, true, false, false] := by
  exact (automaticFlags_same _ _ cSpec2_1_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_21

private abbrev cSpec2_6_1 := specAt2 6 1
private theorem cFlags2_6_1 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_1 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_1

private abbrev cSpec2_6_2 := specAt2 6 2
private theorem cFlags2_6_2 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_2 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec2_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_2

private abbrev cSpec2_6_3 := specAt2 6 3
private theorem cFlags2_6_3 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_3 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_3

private abbrev cSpec2_6_4 := specAt2 6 4
private theorem cFlags2_6_4 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_4 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_4

private abbrev cSpec2_6_5 := specAt2 6 5
private theorem cFlags2_6_5 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_5 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec2_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_5

private abbrev cSpec2_6_6 := specAt2 6 6
private theorem cFlags2_6_6 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_6 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_6

private abbrev cSpec2_6_7 := specAt2 6 7
private theorem cFlags2_6_7 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_7 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_7

private abbrev cSpec2_6_8 := specAt2 6 8
private theorem cFlags2_6_8 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_8 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_8

private abbrev cSpec2_6_9 := specAt2 6 9
private theorem cFlags2_6_9 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_9 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_9

private abbrev cSpec2_6_10 := specAt2 6 10
private theorem cFlags2_6_10 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_10 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_10

private abbrev cSpec2_6_11 := specAt2 6 11
private theorem cFlags2_6_11 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_11 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_5_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_5_11

private abbrev cSpec2_6_12 := specAt2 6 12
private theorem cFlags2_6_12 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_12 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec2_5_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_5_12

private abbrev cSpec2_6_13 := specAt2 6 13
private theorem cFlags2_6_13 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_13 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_5_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_5_13

private abbrev cSpec2_6_14 := specAt2 6 14
private theorem cFlags2_6_14 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_14 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_5_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_5_14

private abbrev cSpec2_6_15 := specAt2 6 15
private theorem cFlags2_6_15 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_15 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec2_5_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_5_15

private abbrev cSpec2_6_16 := specAt2 6 16
private theorem cFlags2_6_16 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_16 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_16

private abbrev cSpec2_6_17 := specAt2 6 17
private theorem cFlags2_6_17 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_17

private abbrev cSpec2_6_18 := specAt2 6 18
private theorem cFlags2_6_18 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_18 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_18

private abbrev cSpec2_6_19 := specAt2 6 19
private theorem cFlags2_6_19 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_19 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_19

private abbrev cSpec2_6_20 := specAt2 6 20
private theorem cFlags2_6_20 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_20 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_20

private abbrev cSpec2_6_21 := specAt2 6 21
private theorem cFlags2_6_21 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_21 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_21

private abbrev cSpec2_6_22 := specAt2 6 22
private theorem cFlags2_6_22 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_22 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_22

private abbrev cSpec2_6_23 := specAt2 6 23
private theorem cFlags2_6_23 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_23 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_23

private abbrev cSpec2_6_24 := specAt2 6 24
private theorem cFlags2_6_24 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_24 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_24

private abbrev cSpec2_6_25 := specAt2 6 25
private theorem cFlags2_6_25 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_25 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_25

private abbrev cSpec2_6_26 := specAt2 6 26
private theorem cFlags2_6_26 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_11

private abbrev cSpec2_6_27 := specAt2 6 27
private theorem cFlags2_6_27 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec2_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_12

private abbrev cSpec2_6_28 := specAt2 6 28
private theorem cFlags2_6_28 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_13

private abbrev cSpec2_6_29 := specAt2 6 29
private theorem cFlags2_6_29 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_14

private abbrev cSpec2_6_30 := specAt2 6 30
private theorem cFlags2_6_30 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_1_15

private abbrev cSpec2_6_31 := specAt2 6 31
private theorem cFlags2_6_31 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_31 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_2_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_16

private abbrev cSpec2_6_32 := specAt2 6 32
private theorem cFlags2_6_32 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_32 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_2_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_17

private abbrev cSpec2_6_33 := specAt2 6 33
private theorem cFlags2_6_33 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_33 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_2_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_18

private abbrev cSpec2_6_34 := specAt2 6 34
private theorem cFlags2_6_34 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_34 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_2_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_19

private abbrev cSpec2_6_35 := specAt2 6 35
private theorem cFlags2_6_35 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_35 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_2_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_20

private abbrev cSpec2_6_36 := specAt2 6 36
private theorem cFlags2_6_36 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_36 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_2_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_21

private abbrev cSpec2_6_37 := specAt2 6 37
private theorem cFlags2_6_37 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_37 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_2_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_22

private abbrev cSpec2_6_38 := specAt2 6 38
private theorem cFlags2_6_38 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_38 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_2_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_23

private abbrev cSpec2_6_39 := specAt2 6 39
private theorem cFlags2_6_39 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_39 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec2_2_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_24

private abbrev cSpec2_6_40 := specAt2 6 40
private theorem cFlags2_6_40 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_40 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec2_2_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_25

private abbrev cSpec2_6_41 := specAt2 6 41
private theorem cFlags2_6_41 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_41 = (List.replicate 8 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_31

private abbrev cSpec2_6_42 := specAt2 6 42
private theorem cFlags2_6_42 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_42 = (List.replicate 5 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_32

private abbrev cSpec2_6_43 := specAt2 6 43
private theorem cFlags2_6_43 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_43 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec2_5_33 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_5_33

private abbrev cSpec2_6_44 := specAt2 6 44
private theorem cFlags2_6_44 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_44 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec2_5_34 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_5_34

private abbrev cSpec2_6_45 := specAt2 6 45
private theorem cFlags2_6_45 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_45 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec2_5_35 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_5_35

private abbrev cSpec2_6_46 := specAt2 6 46
private theorem cFlags2_6_46 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_46 = (List.replicate 8 false) := by
  exact (automaticFlags_same _ _ cSpec2_5_36 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_5_36

private abbrev cSpec2_6_47 := specAt2 6 47
private theorem cFlags2_6_47 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_47 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_3_37 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_37

private abbrev cSpec2_6_48 := specAt2 6 48
private theorem cFlags2_6_48 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_48 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_38 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_38

private abbrev cSpec2_6_49 := specAt2 6 49
private theorem cFlags2_6_49 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_49 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_39 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_39

private abbrev cSpec2_6_50 := specAt2 6 50
private theorem cFlags2_6_50 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_50 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec2_3_40 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_3_40

private abbrev cSpec2_6_51 := specAt2 6 51
private theorem cFlags2_6_51 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_51 = [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false] := by
  exact (automaticFlags_same _ _ cSpec2_2_30 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_30

private abbrev cSpec2_6_52 := specAt2 6 52
private theorem cFlags2_6_52 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_52 = (List.replicate 1 false) := by
  exact (automaticFlags_same _ _ cSpec2_2_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_31

private abbrev cSpec2_6_53 := specAt2 6 53
private theorem cFlags2_6_53 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_53 = (List.replicate 2 true) := by
  exact (automaticFlags_same _ _ cSpec2_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_0_20

private abbrev cSpec2_6_54 := specAt2 6 54
private theorem cFlags2_6_54 : automaticFlags (trunkCatalog.states 2).context cSpec2_6_54 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec2_2_33 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags2_2_33

private theorem keys_eq : coverageKeys (trunkCatalog.states 2) = checkedKeys := by
  rfl
private theorem tasks_eq : coverageTasks (trunkCatalog.states 2) = checkedTasks := by
  rw [← coverageTasksProjection_eq]
  change [(0,[(1, (automaticFlags (trunkCatalog.states 2).context cSpec2_0_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 2).context cSpec2_0_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 2).context cSpec2_0_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 2).context cSpec2_0_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 2).context cSpec2_0_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 2).context cSpec2_0_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 2).context cSpec2_0_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 2).context cSpec2_0_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 2).context cSpec2_0_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 2).context cSpec2_0_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 2).context cSpec2_0_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 2).context cSpec2_0_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 2).context cSpec2_0_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 2).context cSpec2_0_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 2).context cSpec2_0_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 2).context cSpec2_0_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 2).context cSpec2_0_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 2).context cSpec2_0_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 2).context cSpec2_0_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 2).context cSpec2_0_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 2).context cSpec2_0_21).zipIdx.map Prod.swap)]),(1,[(1, (automaticFlags (trunkCatalog.states 2).context cSpec2_1_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 2).context cSpec2_1_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 2).context cSpec2_1_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 2).context cSpec2_1_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 2).context cSpec2_1_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 2).context cSpec2_1_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 2).context cSpec2_1_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 2).context cSpec2_1_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 2).context cSpec2_1_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 2).context cSpec2_1_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 2).context cSpec2_1_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 2).context cSpec2_1_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 2).context cSpec2_1_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 2).context cSpec2_1_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 2).context cSpec2_1_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 2).context cSpec2_1_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 2).context cSpec2_1_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 2).context cSpec2_1_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 2).context cSpec2_1_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 2).context cSpec2_1_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 2).context cSpec2_1_21).zipIdx.map Prod.swap)]),(2,[(1, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 2).context cSpec2_2_33).zipIdx.map Prod.swap)]),(3,[(1, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 2).context cSpec2_3_42).zipIdx.map Prod.swap)]),(4,[(1, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_42).zipIdx.map Prod.swap),(43, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_43).zipIdx.map Prod.swap),(44, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_44).zipIdx.map Prod.swap),(45, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_45).zipIdx.map Prod.swap),(46, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_46).zipIdx.map Prod.swap),(47, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_47).zipIdx.map Prod.swap),(48, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_48).zipIdx.map Prod.swap),(49, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_49).zipIdx.map Prod.swap),(50, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_50).zipIdx.map Prod.swap),(51, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_51).zipIdx.map Prod.swap),(52, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_52).zipIdx.map Prod.swap),(53, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_53).zipIdx.map Prod.swap),(54, (automaticFlags (trunkCatalog.states 2).context cSpec2_4_54).zipIdx.map Prod.swap)]),(5,[(1, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 2).context cSpec2_5_42).zipIdx.map Prod.swap)]),(6,[(1, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_42).zipIdx.map Prod.swap),(43, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_43).zipIdx.map Prod.swap),(44, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_44).zipIdx.map Prod.swap),(45, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_45).zipIdx.map Prod.swap),(46, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_46).zipIdx.map Prod.swap),(47, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_47).zipIdx.map Prod.swap),(48, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_48).zipIdx.map Prod.swap),(49, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_49).zipIdx.map Prod.swap),(50, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_50).zipIdx.map Prod.swap),(51, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_51).zipIdx.map Prod.swap),(52, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_52).zipIdx.map Prod.swap),(53, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_53).zipIdx.map Prod.swap),(54, (automaticFlags (trunkCatalog.states 2).context cSpec2_6_54).zipIdx.map Prod.swap)])] = checkedTasks
  rw [cFlags2_0_1, cFlags2_0_2, cFlags2_0_3, cFlags2_0_4, cFlags2_0_5, cFlags2_0_6, cFlags2_0_7, cFlags2_0_8, cFlags2_0_9, cFlags2_0_10, cFlags2_0_11, cFlags2_0_12, cFlags2_0_13, cFlags2_0_14, cFlags2_0_15, cFlags2_0_16, cFlags2_0_17, cFlags2_0_18, cFlags2_0_19, cFlags2_0_20, cFlags2_0_21, cFlags2_1_1, cFlags2_1_2, cFlags2_1_3, cFlags2_1_4, cFlags2_1_5, cFlags2_1_6, cFlags2_1_7, cFlags2_1_8, cFlags2_1_9, cFlags2_1_10, cFlags2_1_11, cFlags2_1_12, cFlags2_1_13, cFlags2_1_14, cFlags2_1_15, cFlags2_1_16, cFlags2_1_17, cFlags2_1_18, cFlags2_1_19, cFlags2_1_20, cFlags2_1_21, cFlags2_2_1, cFlags2_2_2, cFlags2_2_3, cFlags2_2_4, cFlags2_2_5, cFlags2_2_6, cFlags2_2_7, cFlags2_2_8, cFlags2_2_9, cFlags2_2_10, cFlags2_2_11, cFlags2_2_12, cFlags2_2_13, cFlags2_2_14, cFlags2_2_15, cFlags2_2_16, cFlags2_2_17, cFlags2_2_18, cFlags2_2_19, cFlags2_2_20, cFlags2_2_21, cFlags2_2_22, cFlags2_2_23, cFlags2_2_24, cFlags2_2_25, cFlags2_2_26, cFlags2_2_27, cFlags2_2_28, cFlags2_2_29, cFlags2_2_30, cFlags2_2_31, cFlags2_2_32, cFlags2_2_33, cFlags2_3_1, cFlags2_3_2, cFlags2_3_3, cFlags2_3_4, cFlags2_3_5, cFlags2_3_6, cFlags2_3_7, cFlags2_3_8, cFlags2_3_9, cFlags2_3_10, cFlags2_3_11, cFlags2_3_12, cFlags2_3_13, cFlags2_3_14, cFlags2_3_15, cFlags2_3_16, cFlags2_3_17, cFlags2_3_18, cFlags2_3_19, cFlags2_3_20, cFlags2_3_21, cFlags2_3_22, cFlags2_3_23, cFlags2_3_24, cFlags2_3_25, cFlags2_3_26, cFlags2_3_27, cFlags2_3_28, cFlags2_3_29, cFlags2_3_30, cFlags2_3_31, cFlags2_3_32, cFlags2_3_33, cFlags2_3_34, cFlags2_3_35, cFlags2_3_36, cFlags2_3_37, cFlags2_3_38, cFlags2_3_39, cFlags2_3_40, cFlags2_3_41, cFlags2_3_42, cFlags2_4_1, cFlags2_4_2, cFlags2_4_3, cFlags2_4_4, cFlags2_4_5, cFlags2_4_6, cFlags2_4_7, cFlags2_4_8, cFlags2_4_9, cFlags2_4_10, cFlags2_4_11, cFlags2_4_12, cFlags2_4_13, cFlags2_4_14, cFlags2_4_15, cFlags2_4_16, cFlags2_4_17, cFlags2_4_18, cFlags2_4_19, cFlags2_4_20, cFlags2_4_21, cFlags2_4_22, cFlags2_4_23, cFlags2_4_24, cFlags2_4_25, cFlags2_4_26, cFlags2_4_27, cFlags2_4_28, cFlags2_4_29, cFlags2_4_30, cFlags2_4_31, cFlags2_4_32, cFlags2_4_33, cFlags2_4_34, cFlags2_4_35, cFlags2_4_36, cFlags2_4_37, cFlags2_4_38, cFlags2_4_39, cFlags2_4_40, cFlags2_4_41, cFlags2_4_42, cFlags2_4_43, cFlags2_4_44, cFlags2_4_45, cFlags2_4_46, cFlags2_4_47, cFlags2_4_48, cFlags2_4_49, cFlags2_4_50, cFlags2_4_51, cFlags2_4_52, cFlags2_4_53, cFlags2_4_54, cFlags2_5_1, cFlags2_5_2, cFlags2_5_3, cFlags2_5_4, cFlags2_5_5, cFlags2_5_6, cFlags2_5_7, cFlags2_5_8, cFlags2_5_9, cFlags2_5_10, cFlags2_5_11, cFlags2_5_12, cFlags2_5_13, cFlags2_5_14, cFlags2_5_15, cFlags2_5_16, cFlags2_5_17, cFlags2_5_18, cFlags2_5_19, cFlags2_5_20, cFlags2_5_21, cFlags2_5_22, cFlags2_5_23, cFlags2_5_24, cFlags2_5_25, cFlags2_5_26, cFlags2_5_27, cFlags2_5_28, cFlags2_5_29, cFlags2_5_30, cFlags2_5_31, cFlags2_5_32, cFlags2_5_33, cFlags2_5_34, cFlags2_5_35, cFlags2_5_36, cFlags2_5_37, cFlags2_5_38, cFlags2_5_39, cFlags2_5_40, cFlags2_5_41, cFlags2_5_42, cFlags2_6_1, cFlags2_6_2, cFlags2_6_3, cFlags2_6_4, cFlags2_6_5, cFlags2_6_6, cFlags2_6_7, cFlags2_6_8, cFlags2_6_9, cFlags2_6_10, cFlags2_6_11, cFlags2_6_12, cFlags2_6_13, cFlags2_6_14, cFlags2_6_15, cFlags2_6_16, cFlags2_6_17, cFlags2_6_18, cFlags2_6_19, cFlags2_6_20, cFlags2_6_21, cFlags2_6_22, cFlags2_6_23, cFlags2_6_24, cFlags2_6_25, cFlags2_6_26, cFlags2_6_27, cFlags2_6_28, cFlags2_6_29, cFlags2_6_30, cFlags2_6_31, cFlags2_6_32, cFlags2_6_33, cFlags2_6_34, cFlags2_6_35, cFlags2_6_36, cFlags2_6_37, cFlags2_6_38, cFlags2_6_39, cFlags2_6_40, cFlags2_6_41, cFlags2_6_42, cFlags2_6_43, cFlags2_6_44, cFlags2_6_45, cFlags2_6_46, cFlags2_6_47, cFlags2_6_48, cFlags2_6_49, cFlags2_6_50, cFlags2_6_51, cFlags2_6_52, cFlags2_6_53, cFlags2_6_54]
  rfl
private theorem parents_length : (trunkRawParents (trunkCatalog.states 2).context).length = 100 := by
  decide +kernel
private theorem table_checked : coverageTable checkedKeys checkedTasks 100 := by
  apply coverageRemainder_sound _ _ _ [[74, 99], [], [74, 99], [99], [99], [99], []]
  unfold coverageRemainder parentsFor
  decide +kernel

theorem solution : trunkCoverage trunkCatalog 2 := by
  apply coverageTable_sound 2
  · unfold certRectangleValid; decide +kernel
  · decide +kernel
  · rw [keys_eq, tasks_eq, parents_length]
    exact table_checked
#print axioms solution
