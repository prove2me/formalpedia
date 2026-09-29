-- Prove2me | solution 1 for Freiman.trunk_coverage_04
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:14:54.517905+00:00
-- url     : https://prove2.me/submissions/17503796-861c-4e18-af22-82e61446e9d6

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

private def coordinateFields4 : Array CertField := #[⟨(4/13),(1/13),(0/1),(0/1)⟩,⟨(1/2),(1/6),(0/1),(0/1)⟩,⟨(52/73),(1/73),(0/1),(0/1)⟩,⟨(89/214),(1/214),(0/1),(0/1)⟩,⟨(9/13),(-1/13),(0/1),(0/1)⟩,⟨(2/1),(-1/1),(0/1),(0/1)⟩,⟨(15/37),(-1/37),(0/1),(0/1)⟩,⟨(125/214),(-1/214),(0/1),(0/1)⟩,⟨(66/179),(-1/537),(0/1),(0/1)⟩,⟨(22/37),(1/37),(0/1),(0/1)⟩,⟨(113/179),(1/537),(0/1),(0/1)⟩,⟨(17/22),(-1/22),(0/1),(0/1)⟩,⟨(101/143),(-1/429),(0/1),(0/1)⟩,⟨(735/1006),(1/1006),(0/1),(0/1)⟩,⟨(35/94),(1/94),(0/1),(0/1)⟩,⟨(553/1429),(1/1429),(0/1),(0/1)⟩,⟨(10/23),(-1/69),(0/1),(0/1)⟩,⟨(517/1249),(-1/1249),(0/1),(0/1)⟩,⟨(1272/3013),(1/3013),(0/1),(0/1)⟩,⟨(5/22),(1/22),(0/1),(0/1)⟩,⟨(42/143),(1/429),(0/1),(0/1)⟩,⟨(271/1006),(-1/1006),(0/1),(0/1)⟩,⟨(16/59),(1/177),(0/1),(0/1)⟩,⟨(767/2749),(1/2749),(0/1),(0/1)⟩,⟨(43/142),(-1/142),(0/1),(0/1)⟩,⟨(731/2497),(-1/2497),(0/1),(0/1)⟩,⟨(1809/6094),(1/6094),(0/1),(0/1)⟩,⟨(3289/10753),(1/10753),(0/1),(0/1)⟩,⟨(71/229),(-1/229),(0/1),(0/1)⟩,⟨(1413/4654),(-1/4654),(0/1),(0/1)⟩,⟨(6697/22079),(-1/66237),(0/1),(0/1)⟩,⟨(469/1549),(1/1549),(0/1),(0/1)⟩,⟨(579/1894),(-1/1894),(0/1),(0/1)⟩,⟨(9014/29557),(-1/29557),(0/1),(0/1)⟩,⟨(13/23),(1/69),(0/1),(0/1)⟩,⟨(732/1249),(1/1249),(0/1),(0/1)⟩,⟨(59/94),(-1/94),(0/1),(0/1)⟩]
private abbrev coordinateInput4_0 : LowerPair × Bool × Bool := (([2], []), true, false)
private def coordinateCodes4_0 : List (ℕ × ℕ) := [(0, 1), (0, 1), (0, 2), (0, 1), (3, 1)]
private abbrev coordinateInput4_1 : LowerPair × Bool × Bool := (([1], []), false, false)
private def coordinateCodes4_1 : List (ℕ × ℕ) := [(4, 5), (4, 6), (4, 5), (7, 5), (4, 5)]
private abbrev coordinateInput4_2 : LowerPair × Bool × Bool := (([1], []), true, false)
private def coordinateCodes4_2 : List (ℕ × ℕ) := [(1, 1), (1, 1), (1, 2), (1, 1), (2, 1)]
private abbrev coordinateInput4_3 : LowerPair × Bool × Bool := (([2], []), false, false)
private def coordinateCodes4_3 : List (ℕ × ℕ) := [(6, 5), (6, 6), (6, 5), (8, 5), (6, 5)]
private abbrev coordinateInput4_4 : LowerPair × Bool × Bool := (([1, 1], []), true, false)
private def coordinateCodes4_4 : List (ℕ × ℕ) := [(9, 1), (9, 2), (9, 1), (10, 1)]
private abbrev coordinateInput4_5 : LowerPair × Bool × Bool := (([1, 2], []), false, false)
private def coordinateCodes4_5 : List (ℕ × ℕ) := [(11, 5), (11, 6), (11, 5), (12, 5)]
private abbrev coordinateInput4_6 : LowerPair × Bool × Bool := (([1, 2], []), true, false)
private def coordinateCodes4_6 : List (ℕ × ℕ) := [(2, 1), (2, 2), (2, 1), (13, 1)]
private abbrev coordinateInput4_7 : LowerPair × Bool × Bool := (([1, 1], []), false, false)
private def coordinateCodes4_7 : List (ℕ × ℕ) := [(4, 5), (4, 6), (4, 5), (7, 5)]
private abbrev coordinateInput4_8 : LowerPair × Bool × Bool := (([1], [1]), true, true)
private def coordinateCodes4_8 : List (ℕ × ℕ) := [(1, 1), (1, 2), (1, 1), (2, 1)]
private abbrev coordinateInput4_9 : LowerPair × Bool × Bool := (([1], [2]), false, true)
private def coordinateCodes4_9 : List (ℕ × ℕ) := [(4, 6), (4, 8), (4, 6), (7, 6)]
private abbrev coordinateInput4_10 : LowerPair × Bool × Bool := (([1], [2]), true, true)
private def coordinateCodes4_10 : List (ℕ × ℕ) := [(1, 0), (1, 3), (1, 0), (2, 0)]
private abbrev coordinateInput4_11 : LowerPair × Bool × Bool := (([1], [1]), false, true)
private def coordinateCodes4_11 : List (ℕ × ℕ) := [(4, 4), (4, 7), (4, 4), (7, 4)]
private abbrev coordinateInput4_12 : LowerPair × Bool × Bool := (([2, 1], []), true, false)
private def coordinateCodes4_12 : List (ℕ × ℕ) := [(14, 1), (14, 2), (14, 1), (15, 1)]
private abbrev coordinateInput4_13 : LowerPair × Bool × Bool := (([2, 2], []), false, false)
private def coordinateCodes4_13 : List (ℕ × ℕ) := [(16, 5), (16, 6), (16, 5), (17, 5)]
private abbrev coordinateInput4_14 : LowerPair × Bool × Bool := (([2, 2], []), true, false)
private def coordinateCodes4_14 : List (ℕ × ℕ) := [(3, 1), (3, 2), (3, 1), (18, 1)]
private abbrev coordinateInput4_15 : LowerPair × Bool × Bool := (([2, 1], []), false, false)
private def coordinateCodes4_15 : List (ℕ × ℕ) := [(6, 5), (6, 6), (6, 5), (8, 5)]
private abbrev coordinateInput4_16 : LowerPair × Bool × Bool := (([2], [1]), true, true)
private def coordinateCodes4_16 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 1), (3, 1)]
private abbrev coordinateInput4_17 : LowerPair × Bool × Bool := (([2], [2]), false, true)
private def coordinateCodes4_17 : List (ℕ × ℕ) := [(6, 6), (6, 8), (6, 6), (8, 6)]
private abbrev coordinateInput4_18 : LowerPair × Bool × Bool := (([2], [2]), true, true)
private def coordinateCodes4_18 : List (ℕ × ℕ) := [(0, 0), (0, 3), (0, 0), (3, 0)]
private abbrev coordinateInput4_19 : LowerPair × Bool × Bool := (([2], [1]), false, true)
private def coordinateCodes4_19 : List (ℕ × ℕ) := [(6, 4), (6, 7), (6, 4), (8, 4)]
private abbrev coordinateInput4_20 : LowerPair × Bool × Bool := (([3], []), true, false)
private def coordinateCodes4_20 : List (ℕ × ℕ) := [(19, 1), (19, 1), (19, 2), (19, 1), (20, 1)]
private abbrev coordinateInput4_21 : LowerPair × Bool × Bool := (([3], []), false, false)
private def coordinateCodes4_21 : List (ℕ × ℕ) := [(21, 5), (21, 5)]
private abbrev coordinateInput4_22 : LowerPair × Bool × Bool := (([3, 1], []), true, false)
private def coordinateCodes4_22 : List (ℕ × ℕ) := [(22, 1), (22, 2), (22, 1), (23, 1)]
private abbrev coordinateInput4_23 : LowerPair × Bool × Bool := (([3, 2], []), false, false)
private def coordinateCodes4_23 : List (ℕ × ℕ) := [(24, 5), (24, 6), (24, 5), (25, 5)]
private abbrev coordinateInput4_24 : LowerPair × Bool × Bool := (([3, 2], []), true, false)
private def coordinateCodes4_24 : List (ℕ × ℕ) := [(20, 1), (20, 2), (20, 1), (26, 1)]
private abbrev coordinateInput4_25 : LowerPair × Bool × Bool := (([3, 1], []), false, false)
private def coordinateCodes4_25 : List (ℕ × ℕ) := [(21, 5)]
private abbrev coordinateInput4_26 : LowerPair × Bool × Bool := (([3], [1]), true, true)
private def coordinateCodes4_26 : List (ℕ × ℕ) := [(19, 1), (19, 2), (19, 1), (20, 1)]
private abbrev coordinateInput4_27 : LowerPair × Bool × Bool := (([3], [2]), false, true)
private def coordinateCodes4_27 : List (ℕ × ℕ) := [(21, 6)]
private abbrev coordinateInput4_28 : LowerPair × Bool × Bool := (([3], [2]), true, true)
private def coordinateCodes4_28 : List (ℕ × ℕ) := [(19, 0), (19, 3), (19, 0), (20, 0)]
private abbrev coordinateInput4_29 : LowerPair × Bool × Bool := (([3], [1]), false, true)
private def coordinateCodes4_29 : List (ℕ × ℕ) := [(21, 4)]
private abbrev coordinateInput4_30 : LowerPair × Bool × Bool := (([], []), true, false)
private def coordinateCodes4_30 : List (ℕ × ℕ) := [(1, 1), (1, 2), (1, 1), (2, 1)]
private abbrev coordinateInput4_31 : LowerPair × Bool × Bool := (([], []), false, false)
private def coordinateCodes4_31 : List (ℕ × ℕ) := [(5, 5), (5, 6), (5, 5), (6, 5)]
private abbrev coordinateInput4_32 : LowerPair × Bool × Bool := (([3], [2]), true, false)
private def coordinateCodes4_32 : List (ℕ × ℕ) := [(19, 0), (19, 3), (19, 0), (20, 0)]
private abbrev coordinateInput4_33 : LowerPair × Bool × Bool := (([3], [2]), false, false)
private def coordinateCodes4_33 : List (ℕ × ℕ) := [(21, 6)]
private abbrev coordinateInput4_34 : LowerPair × Bool × Bool := (([3, 1], [2]), true, false)
private def coordinateCodes4_34 : List (ℕ × ℕ) := [(22, 0), (22, 3), (22, 0), (23, 0), (22, 0)]
private abbrev coordinateInput4_35 : LowerPair × Bool × Bool := (([3, 2], [2]), false, false)
private def coordinateCodes4_35 : List (ℕ × ℕ) := [(24, 6), (24, 6), (24, 8), (24, 6), (25, 6)]
private abbrev coordinateInput4_36 : LowerPair × Bool × Bool := (([3, 2], [2]), true, false)
private def coordinateCodes4_36 : List (ℕ × ℕ) := [(20, 0), (20, 3), (20, 0), (26, 0), (20, 0)]
private abbrev coordinateInput4_37 : LowerPair × Bool × Bool := (([3, 1], [2]), false, false)
private def coordinateCodes4_37 : List (ℕ × ℕ) := [(21, 6), (21, 6)]
private abbrev coordinateInput4_38 : LowerPair × Bool × Bool := (([3], [2, 1]), true, true)
private def coordinateCodes4_38 : List (ℕ × ℕ) := [(19, 14), (19, 14), (19, 15), (19, 14), (20, 14)]
private abbrev coordinateInput4_39 : LowerPair × Bool × Bool := (([3], [2, 2]), false, true)
private def coordinateCodes4_39 : List (ℕ × ℕ) := [(21, 16), (21, 16)]
private abbrev coordinateInput4_40 : LowerPair × Bool × Bool := (([3], [2, 2]), true, true)
private def coordinateCodes4_40 : List (ℕ × ℕ) := [(19, 3), (19, 3), (19, 18), (19, 3), (20, 3)]
private abbrev coordinateInput4_41 : LowerPair × Bool × Bool := (([3], [2, 1]), false, true)
private def coordinateCodes4_41 : List (ℕ × ℕ) := [(21, 6), (21, 6)]
private abbrev coordinateInput4_42 : LowerPair × Bool × Bool := (([3, 3], [3, 3]), true, false)
private def coordinateCodes4_42 : List (ℕ × ℕ) := [(27, 27)]
private abbrev coordinateInput4_43 : LowerPair × Bool × Bool := (([3, 3], [3, 3]), false, false)
private def coordinateCodes4_43 : List (ℕ × ℕ) := [(28, 28), (28, 29), (28, 28), (29, 28)]
private abbrev coordinateInput4_44 : LowerPair × Bool × Bool := (([3, 3, 1], [3, 3]), true, false)
private def coordinateCodes4_44 : List (ℕ × ℕ) := [(27, 27), (27, 27)]
private abbrev coordinateInput4_45 : LowerPair × Bool × Bool := (([3, 3, 2], [3, 3]), false, false)
private def coordinateCodes4_45 : List (ℕ × ℕ) := [(29, 28), (29, 29), (29, 28), (30, 28), (29, 28)]
private abbrev coordinateInput4_46 : LowerPair × Bool × Bool := (([3, 3, 2], [3, 3]), true, false)
private def coordinateCodes4_46 : List (ℕ × ℕ) := [(31, 27), (31, 27)]
private abbrev coordinateInput4_47 : LowerPair × Bool × Bool := (([3, 3, 1], [3, 3]), false, false)
private def coordinateCodes4_47 : List (ℕ × ℕ) := [(32, 28), (32, 29), (32, 28), (33, 28), (32, 28)]
private abbrev coordinateInput4_48 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 1]), true, true)
private def coordinateCodes4_48 : List (ℕ × ℕ) := [(27, 27), (27, 27)]
private abbrev coordinateInput4_49 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 2]), false, true)
private def coordinateCodes4_49 : List (ℕ × ℕ) := [(28, 29), (28, 29), (28, 30), (28, 29), (29, 29)]
private abbrev coordinateInput4_50 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 2]), true, true)
private def coordinateCodes4_50 : List (ℕ × ℕ) := [(27, 31), (27, 31)]
private abbrev coordinateInput4_51 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 1]), false, true)
private def coordinateCodes4_51 : List (ℕ × ℕ) := [(28, 32), (28, 32), (28, 33), (28, 32), (29, 32)]
private abbrev coordinateInput4_52 : LowerPair × Bool × Bool := (([3], [3]), true, false)
private def coordinateCodes4_52 : List (ℕ × ℕ) := [(19, 19), (19, 20), (19, 19), (20, 19)]
private abbrev coordinateInput4_53 : LowerPair × Bool × Bool := (([3], [3]), false, false)
private def coordinateCodes4_53 : List (ℕ × ℕ) := [(21, 21)]
private abbrev coordinateInput4_54 : LowerPair × Bool × Bool := (([3, 1], [3]), true, false)
private def coordinateCodes4_54 : List (ℕ × ℕ) := [(22, 19), (22, 20), (22, 19), (23, 19), (22, 19)]
private abbrev coordinateInput4_55 : LowerPair × Bool × Bool := (([3, 2], [3]), false, false)
private def coordinateCodes4_55 : List (ℕ × ℕ) := [(24, 21), (24, 21)]
private abbrev coordinateInput4_56 : LowerPair × Bool × Bool := (([3, 2], [3]), true, false)
private def coordinateCodes4_56 : List (ℕ × ℕ) := [(20, 19), (20, 20), (20, 19), (26, 19), (20, 19)]
private abbrev coordinateInput4_57 : LowerPair × Bool × Bool := (([3, 1], [3]), false, false)
private def coordinateCodes4_57 : List (ℕ × ℕ) := [(21, 21), (21, 21)]
private abbrev coordinateInput4_58 : LowerPair × Bool × Bool := (([3], [3, 1]), true, true)
private def coordinateCodes4_58 : List (ℕ × ℕ) := [(19, 22), (19, 22), (19, 23), (19, 22), (20, 22)]
private abbrev coordinateInput4_59 : LowerPair × Bool × Bool := (([3], [3, 2]), false, true)
private def coordinateCodes4_59 : List (ℕ × ℕ) := [(21, 24), (21, 24)]
private abbrev coordinateInput4_60 : LowerPair × Bool × Bool := (([3], [3, 2]), true, true)
private def coordinateCodes4_60 : List (ℕ × ℕ) := [(19, 20), (19, 20), (19, 26), (19, 20), (20, 20)]
private abbrev coordinateInput4_61 : LowerPair × Bool × Bool := (([3], [3, 1]), false, true)
private def coordinateCodes4_61 : List (ℕ × ℕ) := [(21, 21), (21, 21)]
private abbrev coordinateInput4_62 : LowerPair × Bool × Bool := (([2], [1]), true, false)
private def coordinateCodes4_62 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 1), (3, 1)]
private abbrev coordinateInput4_63 : LowerPair × Bool × Bool := (([2], [1]), false, false)
private def coordinateCodes4_63 : List (ℕ × ℕ) := [(6, 4), (6, 7), (6, 4), (8, 4)]
private abbrev coordinateInput4_64 : LowerPair × Bool × Bool := (([2, 1], [1]), true, false)
private def coordinateCodes4_64 : List (ℕ × ℕ) := [(14, 1), (14, 2), (14, 1), (15, 1), (14, 1)]
private abbrev coordinateInput4_65 : LowerPair × Bool × Bool := (([2, 2], [1]), false, false)
private def coordinateCodes4_65 : List (ℕ × ℕ) := [(16, 4), (16, 4), (16, 7), (16, 4), (17, 4)]
private abbrev coordinateInput4_66 : LowerPair × Bool × Bool := (([2, 2], [1]), true, false)
private def coordinateCodes4_66 : List (ℕ × ℕ) := [(3, 1), (3, 2), (3, 1), (18, 1), (3, 1)]
private abbrev coordinateInput4_67 : LowerPair × Bool × Bool := (([2, 1], [1]), false, false)
private def coordinateCodes4_67 : List (ℕ × ℕ) := [(6, 4), (6, 4), (6, 7), (6, 4), (8, 4)]
private abbrev coordinateInput4_68 : LowerPair × Bool × Bool := (([2], [1, 1]), true, true)
private def coordinateCodes4_68 : List (ℕ × ℕ) := [(0, 9), (0, 9), (0, 10), (0, 9), (3, 9)]
private abbrev coordinateInput4_69 : LowerPair × Bool × Bool := (([2], [1, 2]), false, true)
private def coordinateCodes4_69 : List (ℕ × ℕ) := [(6, 11), (6, 12), (6, 11), (8, 11), (6, 11)]
private abbrev coordinateInput4_70 : LowerPair × Bool × Bool := (([2], [1, 2]), true, true)
private def coordinateCodes4_70 : List (ℕ × ℕ) := [(0, 2), (0, 2), (0, 13), (0, 2), (3, 2)]
private abbrev coordinateInput4_71 : LowerPair × Bool × Bool := (([2], [1, 1]), false, true)
private def coordinateCodes4_71 : List (ℕ × ℕ) := [(6, 4), (6, 7), (6, 4), (8, 4), (6, 4)]
private abbrev coordinateInput4_72 : LowerPair × Bool × Bool := (([3], [1]), true, false)
private def coordinateCodes4_72 : List (ℕ × ℕ) := [(19, 1), (19, 2), (19, 1), (20, 1)]
private abbrev coordinateInput4_73 : LowerPair × Bool × Bool := (([3], [1]), false, false)
private def coordinateCodes4_73 : List (ℕ × ℕ) := [(21, 4)]
private abbrev coordinateInput4_74 : LowerPair × Bool × Bool := (([3, 1], [1]), true, false)
private def coordinateCodes4_74 : List (ℕ × ℕ) := [(22, 1), (22, 2), (22, 1), (23, 1), (22, 1)]
private abbrev coordinateInput4_75 : LowerPair × Bool × Bool := (([3, 2], [1]), false, false)
private def coordinateCodes4_75 : List (ℕ × ℕ) := [(24, 4), (24, 4), (24, 7), (24, 4), (25, 4)]
private abbrev coordinateInput4_76 : LowerPair × Bool × Bool := (([3, 2], [1]), true, false)
private def coordinateCodes4_76 : List (ℕ × ℕ) := [(20, 1), (20, 2), (20, 1), (26, 1), (20, 1)]
private abbrev coordinateInput4_77 : LowerPair × Bool × Bool := (([3, 1], [1]), false, false)
private def coordinateCodes4_77 : List (ℕ × ℕ) := [(21, 4), (21, 4)]
private abbrev coordinateInput4_78 : LowerPair × Bool × Bool := (([3], [1, 1]), true, true)
private def coordinateCodes4_78 : List (ℕ × ℕ) := [(19, 9), (19, 9), (19, 10), (19, 9), (20, 9)]
private abbrev coordinateInput4_79 : LowerPair × Bool × Bool := (([3], [1, 2]), false, true)
private def coordinateCodes4_79 : List (ℕ × ℕ) := [(21, 11), (21, 11)]
private abbrev coordinateInput4_80 : LowerPair × Bool × Bool := (([3], [1, 2]), true, true)
private def coordinateCodes4_80 : List (ℕ × ℕ) := [(19, 2), (19, 2), (19, 13), (19, 2), (20, 2)]
private abbrev coordinateInput4_81 : LowerPair × Bool × Bool := (([3], [1, 1]), false, true)
private def coordinateCodes4_81 : List (ℕ × ℕ) := [(21, 4), (21, 4)]
private abbrev coordinateInput4_82 : LowerPair × Bool × Bool := (([2], [2]), true, false)
private def coordinateCodes4_82 : List (ℕ × ℕ) := [(0, 0), (0, 3), (0, 0), (3, 0)]
private abbrev coordinateInput4_83 : LowerPair × Bool × Bool := (([2], [2]), false, false)
private def coordinateCodes4_83 : List (ℕ × ℕ) := [(6, 6), (6, 8), (6, 6), (8, 6)]
private abbrev coordinateInput4_84 : LowerPair × Bool × Bool := (([2, 1], [2]), true, false)
private def coordinateCodes4_84 : List (ℕ × ℕ) := [(14, 0), (14, 3), (14, 0), (15, 0), (14, 0)]
private abbrev coordinateInput4_85 : LowerPair × Bool × Bool := (([2, 2], [2]), false, false)
private def coordinateCodes4_85 : List (ℕ × ℕ) := [(16, 6), (16, 6), (16, 8), (16, 6), (17, 6)]
private abbrev coordinateInput4_86 : LowerPair × Bool × Bool := (([2, 2], [2]), true, false)
private def coordinateCodes4_86 : List (ℕ × ℕ) := [(3, 0), (3, 3), (3, 0), (18, 0), (3, 0)]
private abbrev coordinateInput4_87 : LowerPair × Bool × Bool := (([2, 1], [2]), false, false)
private def coordinateCodes4_87 : List (ℕ × ℕ) := [(6, 6), (6, 6), (6, 8), (6, 6), (8, 6)]
private abbrev coordinateInput4_88 : LowerPair × Bool × Bool := (([2], [2, 1]), true, true)
private def coordinateCodes4_88 : List (ℕ × ℕ) := [(0, 14), (0, 14), (0, 15), (0, 14), (3, 14)]
private abbrev coordinateInput4_89 : LowerPair × Bool × Bool := (([2], [2, 2]), false, true)
private def coordinateCodes4_89 : List (ℕ × ℕ) := [(6, 16), (6, 17), (6, 16), (8, 16), (6, 16)]
private abbrev coordinateInput4_90 : LowerPair × Bool × Bool := (([2], [2, 2]), true, true)
private def coordinateCodes4_90 : List (ℕ × ℕ) := [(0, 3), (0, 3), (0, 18), (0, 3), (3, 3)]
private abbrev coordinateInput4_91 : LowerPair × Bool × Bool := (([2], [2, 1]), false, true)
private def coordinateCodes4_91 : List (ℕ × ℕ) := [(6, 6), (6, 8), (6, 6), (8, 6), (6, 6)]
private abbrev coordinateInput4_92 : LowerPair × Bool × Bool := (([2], [3]), true, false)
private def coordinateCodes4_92 : List (ℕ × ℕ) := [(0, 19), (0, 20), (0, 19), (3, 19)]
private abbrev coordinateInput4_93 : LowerPair × Bool × Bool := (([2], [3]), false, false)
private def coordinateCodes4_93 : List (ℕ × ℕ) := [(6, 21)]
private abbrev coordinateInput4_94 : LowerPair × Bool × Bool := (([2, 1], [3]), true, false)
private def coordinateCodes4_94 : List (ℕ × ℕ) := [(14, 19), (14, 20), (14, 19), (15, 19), (14, 19)]
private abbrev coordinateInput4_95 : LowerPair × Bool × Bool := (([2, 2], [3]), false, false)
private def coordinateCodes4_95 : List (ℕ × ℕ) := [(16, 21), (16, 21)]
private abbrev coordinateInput4_96 : LowerPair × Bool × Bool := (([2, 2], [3]), true, false)
private def coordinateCodes4_96 : List (ℕ × ℕ) := [(3, 19), (3, 20), (3, 19), (18, 19), (3, 19)]
private abbrev coordinateInput4_97 : LowerPair × Bool × Bool := (([2, 1], [3]), false, false)
private def coordinateCodes4_97 : List (ℕ × ℕ) := [(6, 21), (6, 21)]
private abbrev coordinateInput4_98 : LowerPair × Bool × Bool := (([2], [3, 1]), true, true)
private def coordinateCodes4_98 : List (ℕ × ℕ) := [(0, 22), (0, 22), (0, 23), (0, 22), (3, 22)]
private abbrev coordinateInput4_99 : LowerPair × Bool × Bool := (([2], [3, 2]), false, true)
private def coordinateCodes4_99 : List (ℕ × ℕ) := [(6, 24), (6, 25), (6, 24), (8, 24), (6, 24)]
private abbrev coordinateInput4_100 : LowerPair × Bool × Bool := (([2], [3, 2]), true, true)
private def coordinateCodes4_100 : List (ℕ × ℕ) := [(0, 20), (0, 20), (0, 26), (0, 20), (3, 20)]
private abbrev coordinateInput4_101 : LowerPair × Bool × Bool := (([2], [3, 1]), false, true)
private def coordinateCodes4_101 : List (ℕ × ℕ) := [(6, 21), (6, 21)]
private abbrev coordinateInput4_102 : LowerPair × Bool × Bool := (([3], [1, 1]), true, false)
private def coordinateCodes4_102 : List (ℕ × ℕ) := [(19, 9), (19, 9), (19, 10), (19, 9), (20, 9)]
private abbrev coordinateInput4_103 : LowerPair × Bool × Bool := (([3], [1, 1]), false, false)
private def coordinateCodes4_103 : List (ℕ × ℕ) := [(21, 4), (21, 4)]
private abbrev coordinateInput4_104 : LowerPair × Bool × Bool := (([3, 1], [1, 1]), true, false)
private def coordinateCodes4_104 : List (ℕ × ℕ) := [(22, 9), (22, 10), (22, 9), (23, 9)]
private abbrev coordinateInput4_105 : LowerPair × Bool × Bool := (([3, 2], [1, 1]), false, false)
private def coordinateCodes4_105 : List (ℕ × ℕ) := [(24, 4), (24, 7), (24, 4), (25, 4)]
private abbrev coordinateInput4_106 : LowerPair × Bool × Bool := (([3, 2], [1, 1]), true, false)
private def coordinateCodes4_106 : List (ℕ × ℕ) := [(20, 9), (20, 10), (20, 9), (26, 9)]
private abbrev coordinateInput4_107 : LowerPair × Bool × Bool := (([3, 1], [1, 1]), false, false)
private def coordinateCodes4_107 : List (ℕ × ℕ) := [(21, 4)]
private abbrev coordinateInput4_108 : LowerPair × Bool × Bool := (([3], [1, 1, 1]), true, true)
private def coordinateCodes4_108 : List (ℕ × ℕ) := [(19, 9), (19, 10), (19, 9), (20, 9)]
private abbrev coordinateInput4_109 : LowerPair × Bool × Bool := (([3], [1, 1, 2]), false, true)
private def coordinateCodes4_109 : List (ℕ × ℕ) := [(21, 7)]
private abbrev coordinateInput4_110 : LowerPair × Bool × Bool := (([3], [1, 1, 2]), true, true)
private def coordinateCodes4_110 : List (ℕ × ℕ) := [(19, 34), (19, 35), (19, 34), (20, 34)]
private abbrev coordinateInput4_111 : LowerPair × Bool × Bool := (([3], [1, 1, 1]), false, true)
private def coordinateCodes4_111 : List (ℕ × ℕ) := [(21, 36)]

private def decodeCoordinate4 (x : ℕ × ℕ) : CertField × CertField :=
  (coordinateFields4[x.1]?.getD ⟨0,0,0,0⟩,coordinateFields4[x.2]?.getD ⟨0,0,0,0⟩)

private theorem hCoordinate4_0 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_0.1 coordinateInput4_0.2.1 coordinateInput4_0.2.2).map Prod.fst = coordinateCodes4_0.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_1 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_1.1 coordinateInput4_1.2.1 coordinateInput4_1.2.2).map Prod.fst = coordinateCodes4_1.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_2 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_2.1 coordinateInput4_2.2.1 coordinateInput4_2.2.2).map Prod.fst = coordinateCodes4_2.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_3 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_3.1 coordinateInput4_3.2.1 coordinateInput4_3.2.2).map Prod.fst = coordinateCodes4_3.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_4 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_4.1 coordinateInput4_4.2.1 coordinateInput4_4.2.2).map Prod.fst = coordinateCodes4_4.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_5 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_5.1 coordinateInput4_5.2.1 coordinateInput4_5.2.2).map Prod.fst = coordinateCodes4_5.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_6 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_6.1 coordinateInput4_6.2.1 coordinateInput4_6.2.2).map Prod.fst = coordinateCodes4_6.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_7 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_7.1 coordinateInput4_7.2.1 coordinateInput4_7.2.2).map Prod.fst = coordinateCodes4_7.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_8 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_8.1 coordinateInput4_8.2.1 coordinateInput4_8.2.2).map Prod.fst = coordinateCodes4_8.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_9 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_9.1 coordinateInput4_9.2.1 coordinateInput4_9.2.2).map Prod.fst = coordinateCodes4_9.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_10 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_10.1 coordinateInput4_10.2.1 coordinateInput4_10.2.2).map Prod.fst = coordinateCodes4_10.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_11 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_11.1 coordinateInput4_11.2.1 coordinateInput4_11.2.2).map Prod.fst = coordinateCodes4_11.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_12 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_12.1 coordinateInput4_12.2.1 coordinateInput4_12.2.2).map Prod.fst = coordinateCodes4_12.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_13 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_13.1 coordinateInput4_13.2.1 coordinateInput4_13.2.2).map Prod.fst = coordinateCodes4_13.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_14 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_14.1 coordinateInput4_14.2.1 coordinateInput4_14.2.2).map Prod.fst = coordinateCodes4_14.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_15 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_15.1 coordinateInput4_15.2.1 coordinateInput4_15.2.2).map Prod.fst = coordinateCodes4_15.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_16 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_16.1 coordinateInput4_16.2.1 coordinateInput4_16.2.2).map Prod.fst = coordinateCodes4_16.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_17 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_17.1 coordinateInput4_17.2.1 coordinateInput4_17.2.2).map Prod.fst = coordinateCodes4_17.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_18 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_18.1 coordinateInput4_18.2.1 coordinateInput4_18.2.2).map Prod.fst = coordinateCodes4_18.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_19 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_19.1 coordinateInput4_19.2.1 coordinateInput4_19.2.2).map Prod.fst = coordinateCodes4_19.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_20 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_20.1 coordinateInput4_20.2.1 coordinateInput4_20.2.2).map Prod.fst = coordinateCodes4_20.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_21 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_21.1 coordinateInput4_21.2.1 coordinateInput4_21.2.2).map Prod.fst = coordinateCodes4_21.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_22 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_22.1 coordinateInput4_22.2.1 coordinateInput4_22.2.2).map Prod.fst = coordinateCodes4_22.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_23 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_23.1 coordinateInput4_23.2.1 coordinateInput4_23.2.2).map Prod.fst = coordinateCodes4_23.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_24 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_24.1 coordinateInput4_24.2.1 coordinateInput4_24.2.2).map Prod.fst = coordinateCodes4_24.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_25 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_25.1 coordinateInput4_25.2.1 coordinateInput4_25.2.2).map Prod.fst = coordinateCodes4_25.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_26 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_26.1 coordinateInput4_26.2.1 coordinateInput4_26.2.2).map Prod.fst = coordinateCodes4_26.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_27 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_27.1 coordinateInput4_27.2.1 coordinateInput4_27.2.2).map Prod.fst = coordinateCodes4_27.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_28 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_28.1 coordinateInput4_28.2.1 coordinateInput4_28.2.2).map Prod.fst = coordinateCodes4_28.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_29 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_29.1 coordinateInput4_29.2.1 coordinateInput4_29.2.2).map Prod.fst = coordinateCodes4_29.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_30 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_30.1 coordinateInput4_30.2.1 coordinateInput4_30.2.2).map Prod.fst = coordinateCodes4_30.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_31 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_31.1 coordinateInput4_31.2.1 coordinateInput4_31.2.2).map Prod.fst = coordinateCodes4_31.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_32 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_32.1 coordinateInput4_32.2.1 coordinateInput4_32.2.2).map Prod.fst = coordinateCodes4_32.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_33 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_33.1 coordinateInput4_33.2.1 coordinateInput4_33.2.2).map Prod.fst = coordinateCodes4_33.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_34 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_34.1 coordinateInput4_34.2.1 coordinateInput4_34.2.2).map Prod.fst = coordinateCodes4_34.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_35 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_35.1 coordinateInput4_35.2.1 coordinateInput4_35.2.2).map Prod.fst = coordinateCodes4_35.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_36 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_36.1 coordinateInput4_36.2.1 coordinateInput4_36.2.2).map Prod.fst = coordinateCodes4_36.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_37 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_37.1 coordinateInput4_37.2.1 coordinateInput4_37.2.2).map Prod.fst = coordinateCodes4_37.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_38 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_38.1 coordinateInput4_38.2.1 coordinateInput4_38.2.2).map Prod.fst = coordinateCodes4_38.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_39 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_39.1 coordinateInput4_39.2.1 coordinateInput4_39.2.2).map Prod.fst = coordinateCodes4_39.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_40 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_40.1 coordinateInput4_40.2.1 coordinateInput4_40.2.2).map Prod.fst = coordinateCodes4_40.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_41 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_41.1 coordinateInput4_41.2.1 coordinateInput4_41.2.2).map Prod.fst = coordinateCodes4_41.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_42 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_42.1 coordinateInput4_42.2.1 coordinateInput4_42.2.2).map Prod.fst = coordinateCodes4_42.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_43 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_43.1 coordinateInput4_43.2.1 coordinateInput4_43.2.2).map Prod.fst = coordinateCodes4_43.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_44 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_44.1 coordinateInput4_44.2.1 coordinateInput4_44.2.2).map Prod.fst = coordinateCodes4_44.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_45 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_45.1 coordinateInput4_45.2.1 coordinateInput4_45.2.2).map Prod.fst = coordinateCodes4_45.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_46 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_46.1 coordinateInput4_46.2.1 coordinateInput4_46.2.2).map Prod.fst = coordinateCodes4_46.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_47 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_47.1 coordinateInput4_47.2.1 coordinateInput4_47.2.2).map Prod.fst = coordinateCodes4_47.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_48 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_48.1 coordinateInput4_48.2.1 coordinateInput4_48.2.2).map Prod.fst = coordinateCodes4_48.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_49 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_49.1 coordinateInput4_49.2.1 coordinateInput4_49.2.2).map Prod.fst = coordinateCodes4_49.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_50 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_50.1 coordinateInput4_50.2.1 coordinateInput4_50.2.2).map Prod.fst = coordinateCodes4_50.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_51 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_51.1 coordinateInput4_51.2.1 coordinateInput4_51.2.2).map Prod.fst = coordinateCodes4_51.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_52 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_52.1 coordinateInput4_52.2.1 coordinateInput4_52.2.2).map Prod.fst = coordinateCodes4_52.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_53 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_53.1 coordinateInput4_53.2.1 coordinateInput4_53.2.2).map Prod.fst = coordinateCodes4_53.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_54 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_54.1 coordinateInput4_54.2.1 coordinateInput4_54.2.2).map Prod.fst = coordinateCodes4_54.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_55 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_55.1 coordinateInput4_55.2.1 coordinateInput4_55.2.2).map Prod.fst = coordinateCodes4_55.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_56 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_56.1 coordinateInput4_56.2.1 coordinateInput4_56.2.2).map Prod.fst = coordinateCodes4_56.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_57 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_57.1 coordinateInput4_57.2.1 coordinateInput4_57.2.2).map Prod.fst = coordinateCodes4_57.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_58 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_58.1 coordinateInput4_58.2.1 coordinateInput4_58.2.2).map Prod.fst = coordinateCodes4_58.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_59 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_59.1 coordinateInput4_59.2.1 coordinateInput4_59.2.2).map Prod.fst = coordinateCodes4_59.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_60 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_60.1 coordinateInput4_60.2.1 coordinateInput4_60.2.2).map Prod.fst = coordinateCodes4_60.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_61 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_61.1 coordinateInput4_61.2.1 coordinateInput4_61.2.2).map Prod.fst = coordinateCodes4_61.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_62 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_62.1 coordinateInput4_62.2.1 coordinateInput4_62.2.2).map Prod.fst = coordinateCodes4_62.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_63 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_63.1 coordinateInput4_63.2.1 coordinateInput4_63.2.2).map Prod.fst = coordinateCodes4_63.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_64 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_64.1 coordinateInput4_64.2.1 coordinateInput4_64.2.2).map Prod.fst = coordinateCodes4_64.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_65 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_65.1 coordinateInput4_65.2.1 coordinateInput4_65.2.2).map Prod.fst = coordinateCodes4_65.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_66 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_66.1 coordinateInput4_66.2.1 coordinateInput4_66.2.2).map Prod.fst = coordinateCodes4_66.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_67 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_67.1 coordinateInput4_67.2.1 coordinateInput4_67.2.2).map Prod.fst = coordinateCodes4_67.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_68 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_68.1 coordinateInput4_68.2.1 coordinateInput4_68.2.2).map Prod.fst = coordinateCodes4_68.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_69 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_69.1 coordinateInput4_69.2.1 coordinateInput4_69.2.2).map Prod.fst = coordinateCodes4_69.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_70 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_70.1 coordinateInput4_70.2.1 coordinateInput4_70.2.2).map Prod.fst = coordinateCodes4_70.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_71 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_71.1 coordinateInput4_71.2.1 coordinateInput4_71.2.2).map Prod.fst = coordinateCodes4_71.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_72 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_72.1 coordinateInput4_72.2.1 coordinateInput4_72.2.2).map Prod.fst = coordinateCodes4_72.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_73 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_73.1 coordinateInput4_73.2.1 coordinateInput4_73.2.2).map Prod.fst = coordinateCodes4_73.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_74 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_74.1 coordinateInput4_74.2.1 coordinateInput4_74.2.2).map Prod.fst = coordinateCodes4_74.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_75 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_75.1 coordinateInput4_75.2.1 coordinateInput4_75.2.2).map Prod.fst = coordinateCodes4_75.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_76 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_76.1 coordinateInput4_76.2.1 coordinateInput4_76.2.2).map Prod.fst = coordinateCodes4_76.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_77 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_77.1 coordinateInput4_77.2.1 coordinateInput4_77.2.2).map Prod.fst = coordinateCodes4_77.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_78 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_78.1 coordinateInput4_78.2.1 coordinateInput4_78.2.2).map Prod.fst = coordinateCodes4_78.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_79 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_79.1 coordinateInput4_79.2.1 coordinateInput4_79.2.2).map Prod.fst = coordinateCodes4_79.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_80 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_80.1 coordinateInput4_80.2.1 coordinateInput4_80.2.2).map Prod.fst = coordinateCodes4_80.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_81 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_81.1 coordinateInput4_81.2.1 coordinateInput4_81.2.2).map Prod.fst = coordinateCodes4_81.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_82 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_82.1 coordinateInput4_82.2.1 coordinateInput4_82.2.2).map Prod.fst = coordinateCodes4_82.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_83 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_83.1 coordinateInput4_83.2.1 coordinateInput4_83.2.2).map Prod.fst = coordinateCodes4_83.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_84 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_84.1 coordinateInput4_84.2.1 coordinateInput4_84.2.2).map Prod.fst = coordinateCodes4_84.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_85 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_85.1 coordinateInput4_85.2.1 coordinateInput4_85.2.2).map Prod.fst = coordinateCodes4_85.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_86 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_86.1 coordinateInput4_86.2.1 coordinateInput4_86.2.2).map Prod.fst = coordinateCodes4_86.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_87 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_87.1 coordinateInput4_87.2.1 coordinateInput4_87.2.2).map Prod.fst = coordinateCodes4_87.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_88 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_88.1 coordinateInput4_88.2.1 coordinateInput4_88.2.2).map Prod.fst = coordinateCodes4_88.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_89 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_89.1 coordinateInput4_89.2.1 coordinateInput4_89.2.2).map Prod.fst = coordinateCodes4_89.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_90 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_90.1 coordinateInput4_90.2.1 coordinateInput4_90.2.2).map Prod.fst = coordinateCodes4_90.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_91 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_91.1 coordinateInput4_91.2.1 coordinateInput4_91.2.2).map Prod.fst = coordinateCodes4_91.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_92 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_92.1 coordinateInput4_92.2.1 coordinateInput4_92.2.2).map Prod.fst = coordinateCodes4_92.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_93 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_93.1 coordinateInput4_93.2.1 coordinateInput4_93.2.2).map Prod.fst = coordinateCodes4_93.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_94 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_94.1 coordinateInput4_94.2.1 coordinateInput4_94.2.2).map Prod.fst = coordinateCodes4_94.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_95 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_95.1 coordinateInput4_95.2.1 coordinateInput4_95.2.2).map Prod.fst = coordinateCodes4_95.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_96 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_96.1 coordinateInput4_96.2.1 coordinateInput4_96.2.2).map Prod.fst = coordinateCodes4_96.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_97 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_97.1 coordinateInput4_97.2.1 coordinateInput4_97.2.2).map Prod.fst = coordinateCodes4_97.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_98 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_98.1 coordinateInput4_98.2.1 coordinateInput4_98.2.2).map Prod.fst = coordinateCodes4_98.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_99 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_99.1 coordinateInput4_99.2.1 coordinateInput4_99.2.2).map Prod.fst = coordinateCodes4_99.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_100 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_100.1 coordinateInput4_100.2.1 coordinateInput4_100.2.2).map Prod.fst = coordinateCodes4_100.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_101 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_101.1 coordinateInput4_101.2.1 coordinateInput4_101.2.2).map Prod.fst = coordinateCodes4_101.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_102 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_102.1 coordinateInput4_102.2.1 coordinateInput4_102.2.2).map Prod.fst = coordinateCodes4_102.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_103 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_103.1 coordinateInput4_103.2.1 coordinateInput4_103.2.2).map Prod.fst = coordinateCodes4_103.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_104 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_104.1 coordinateInput4_104.2.1 coordinateInput4_104.2.2).map Prod.fst = coordinateCodes4_104.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_105 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_105.1 coordinateInput4_105.2.1 coordinateInput4_105.2.2).map Prod.fst = coordinateCodes4_105.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_106 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_106.1 coordinateInput4_106.2.1 coordinateInput4_106.2.2).map Prod.fst = coordinateCodes4_106.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_107 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_107.1 coordinateInput4_107.2.1 coordinateInput4_107.2.2).map Prod.fst = coordinateCodes4_107.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_108 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_108.1 coordinateInput4_108.2.1 coordinateInput4_108.2.2).map Prod.fst = coordinateCodes4_108.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_109 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_109.1 coordinateInput4_109.2.1 coordinateInput4_109.2.2).map Prod.fst = coordinateCodes4_109.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_110 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_110.1 coordinateInput4_110.2.1 coordinateInput4_110.2.2).map Prod.fst = coordinateCodes4_110.map decodeCoordinate4 := by decide +kernel

private theorem hCoordinate4_111 :
    (trunkEndpointCases (trunkCatalog.states 4).context coordinateInput4_111.1 coordinateInput4_111.2.1 coordinateInput4_111.2.2).map Prod.fst = coordinateCodes4_111.map decodeCoordinate4 := by decide +kernel

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
private def kp2 : List ℕ := [2, 129]
private def kp3 : List ℕ := [3, 53]
private def kp4 : List ℕ := [4, 9, 14, 19, 24, 29, 34, 39, 44, 49, 54, 59, 64, 69, 74, 79, 84, 89, 94, 99, 104, 109, 114, 119, 124, 125, 126, 127, 128, 130, 131, 132, 133, 135, 136, 137, 138, 140, 141, 142, 143, 145, 146, 147, 148, 150, 151, 152, 153, 155, 156, 157, 158, 160, 161, 162, 163, 165, 166, 167, 168, 170, 171, 172, 173, 175, 176, 177, 178, 180, 181, 182, 183, 185, 186, 187, 188, 190, 191, 192, 193, 195, 196, 197, 198, 200, 201, 202, 203, 205, 206, 207, 208, 210, 211, 212, 213, 215, 216, 217, 218, 220, 221, 222, 223, 225, 226, 227, 228, 230, 231, 232, 233, 235, 236, 237, 238, 240, 241, 242, 243, 245, 246, 247, 248, 250, 251, 252, 253, 255, 256, 257, 258, 260, 261, 262, 263, 265, 266, 267, 268, 270, 271, 272, 273, 275, 276, 277, 278, 280, 281, 282, 283, 285, 286, 287, 288, 290, 291, 292, 293, 295, 296, 297, 298, 300, 301, 302, 303, 305, 306, 307, 308, 310, 311, 312, 313, 315, 316, 317, 318, 320, 321, 322, 323, 325, 326, 327, 328, 330, 331, 332, 333, 335, 336, 337, 338, 340, 341, 342, 343, 345, 346, 347, 348, 350, 351, 352, 353, 355, 356, 357, 358, 360, 361, 362, 363, 365, 366, 367, 368, 370, 371, 372, 373, 375, 376, 377, 378, 380, 381, 382, 383, 385, 386, 387, 388, 390, 391, 392, 393, 395, 396, 397, 398, 400, 401, 402, 403, 405, 406, 407, 408, 410, 411, 412, 413, 415, 416, 417, 418, 420, 421, 422, 423, 425, 426, 427, 428, 430, 431, 432, 433, 435, 436, 437, 438, 440, 441, 442, 443, 445, 446, 447, 448, 450, 451, 452, 453, 455, 456, 457, 458, 460, 461, 462, 463, 465, 466, 467, 468, 470, 471, 472, 473, 475, 476, 477, 478, 480, 481, 482, 483, 485, 486, 487, 488, 490, 491, 492, 493, 495, 496, 497, 498, 500, 501, 502, 503, 505, 506, 507, 508, 510, 511, 512, 513, 515, 516, 517, 518, 520, 521, 522, 523, 525, 526, 527, 528, 530, 531, 532, 533, 535, 536, 537, 538, 540, 541, 542, 543, 545, 546, 547, 548, 550, 551, 552, 553, 555, 556, 557, 558, 560, 561, 562, 563, 565, 566, 567, 568, 570, 571, 572, 573, 575, 576, 577, 578, 580, 581, 582, 583, 585, 586, 587, 588, 590, 591, 592, 593, 595, 596, 597, 598, 600, 601, 602, 603, 605, 606, 607, 608, 610, 611, 612, 613, 615, 616, 617, 618, 620, 621, 622, 623]
private def kp5 : List ℕ := [5, 6, 7, 8, 10, 11, 12, 13, 15, 16, 17, 18, 20, 21, 22, 23, 30, 31, 32, 33, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 48, 55, 56, 57, 58, 60, 61, 62, 63, 65, 66, 67, 68, 70, 71, 72, 73, 80, 81, 82, 83, 85, 86, 87, 88, 90, 91, 92, 93, 95, 96, 97, 98, 100, 101, 102, 103, 134, 139, 144, 149, 159, 164, 169, 174, 184, 189, 194, 199, 209, 214, 219, 224, 229, 259, 264, 269, 274, 284, 289, 294, 299, 309, 314, 319, 324, 334, 339, 344, 349, 354, 384, 389, 394, 399, 409, 414, 419, 424, 434, 439, 444, 449, 459, 464, 469, 474, 479, 509, 514, 519, 524, 534, 539, 544, 549, 559, 564, 569, 574, 584, 589, 594, 599, 604]
private def kp6 : List ℕ := [25]
private def kp7 : List ℕ := [26]
private def kp8 : List ℕ := [27, 154]
private def kp9 : List ℕ := [28]
private def kp10 : List ℕ := [52]
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
private def kp33 : List ℕ := [204]
private def kp34 : List ℕ := [234]
private def kp35 : List ℕ := [239]
private def kp36 : List ℕ := [244]
private def kp37 : List ℕ := [249]
private def kp38 : List ℕ := [254]
private def kp39 : List ℕ := [279]
private def kp40 : List ℕ := [304]
private def kp41 : List ℕ := [329]
private def kp42 : List ℕ := [359]
private def kp43 : List ℕ := [364, 489, 614]
private def kp44 : List ℕ := [369, 494, 619]
private def kp45 : List ℕ := [374, 499, 624]
private def kp46 : List ℕ := [379]
private def kp47 : List ℕ := [404]
private def kp48 : List ℕ := [429, 484]
private def kp49 : List ℕ := [454]
private def kp50 : List ℕ := [504]
private def kp51 : List ℕ := [529]
private def kp52 : List ℕ := [554, 609]
private def kp53 : List ℕ := [579]
private def kp54 : List ℕ := [0, 25, 50, 75, 105, 110]
private def kp55 : List ℕ := [1, 26, 51, 76, 106, 111]
private def kp56 : List ℕ := [2, 129, 254, 379, 504]
private def kp57 : List ℕ := [3, 28, 53, 78, 108, 113]
private def kp58 : List ℕ := [27, 154, 279, 404, 529]
private def kp59 : List ℕ := [52, 77, 107, 112]
private def kp60 : List ℕ := [179, 234, 239]
private def kp61 : List ℕ := [204, 329, 454, 579]
private def kp62 : List ℕ := [304, 429, 554]
private def kp63 : List ℕ := [364]
private def kp64 : List ℕ := [369]
private def kp65 : List ℕ := [374]
private def kp66 : List ℕ := [484]
private def kp67 : List ℕ := [489]
private def kp68 : List ℕ := [494]
private def kp69 : List ℕ := [499]
private def kp70 : List ℕ := [609]
private def kp71 : List ℕ := [614]
private def kp72 : List ℕ := [619]
private def kp73 : List ℕ := [624]
private def kp74 : List ℕ := [0, 25, 50, 75]
private def kp75 : List ℕ := [1, 26, 51, 76]
private def kp76 : List ℕ := [2, 129, 254]
private def kp77 : List ℕ := [3, 28, 53, 78]
private def kp78 : List ℕ := [27, 154, 279]
private def kp79 : List ℕ := [52, 77]
private def kp80 : List ℕ := [204, 329]
private def kp81 : List ℕ := [304, 359, 484, 609]
private def kp82 : List ℕ := [304, 359, 609]
private def kp83 : List ℕ := [359, 484, 609]
private def kp84 : List ℕ := [429]
private def kp85 : List ℕ := [484, 609]
private def kp86 : List ℕ := [554]
private def kp87 : List ℕ := [4, 9, 14, 19, 24, 29, 34, 39, 44, 49, 54, 59, 64, 69, 74, 79, 84, 89, 94, 99, 104, 109, 114, 119, 124, 125, 126, 127, 128, 150, 151, 152, 153, 175, 176, 177, 178, 200, 201, 202, 203, 225, 226, 227, 228, 230, 231, 232, 233, 235, 236, 237, 238, 240, 241, 242, 243, 245, 246, 247, 248, 250, 251, 252, 253, 275, 276, 277, 278, 300, 301, 302, 303, 325, 326, 327, 328, 350, 351, 352, 353, 355, 356, 357, 358, 360, 361, 362, 363, 365, 366, 367, 368, 370, 371, 372, 373, 375, 376, 377, 378, 400, 401, 402, 403, 425, 426, 427, 428, 450, 451, 452, 453, 475, 476, 477, 478, 480, 481, 482, 483, 485, 486, 487, 488, 490, 491, 492, 493, 495, 496, 497, 498, 500, 501, 502, 503, 525, 526, 527, 528, 550, 551, 552, 553, 575, 576, 577, 578, 600, 601, 602, 603, 605, 606, 607, 608, 610, 611, 612, 613, 615, 616, 617, 618, 620, 621, 622, 623]
private def kp88 : List ℕ := [5, 6, 7, 8, 10, 11, 12, 13, 15, 16, 17, 18, 20, 21, 22, 23, 30, 31, 32, 33, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 48, 55, 56, 57, 58, 60, 61, 62, 63, 65, 66, 67, 68, 70, 71, 72, 73, 80, 81, 82, 83, 85, 86, 87, 88, 90, 91, 92, 93, 95, 96, 97, 98, 100, 101, 102, 103, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 229, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 354, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 479, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 604]
private def kp89 : List ℕ := [484, 489]
private def kp90 : List ℕ := [0, 25, 50, 75, 105]
private def kp91 : List ℕ := [1, 26, 51, 76, 106]
private def kp92 : List ℕ := [3, 28, 53, 78, 108]
private def kp93 : List ℕ := [52, 77, 107]
private def kp94 : List ℕ := [179, 234]
private def kp95 : List ℕ := [359, 364]
private def kp96 : List ℕ := [609, 614]
private def kb0 : List ℤ := [-1]
private def kb1 : List ℤ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
private def kb2 : List ℤ := [0, 1, 2, 3]
private def kb3 : List ℤ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
private def kb4 : List ℤ := [8, 10, 11, 16, 17, 18]
private def kb5 : List ℤ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
private def kb6 : List ℤ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
private def kb7 : List ℤ := [0, 2, 3]
private def kb8 : List ℤ := [12, 13, 14, 15]
private def kb9 : List ℤ := [0]
private def kb10 : List ℤ := [0, 1, 2, 3, 4, 5, 6, 7]
private def pk0 : List CoverageKey := [(0,kp0,0,kb0),(0,kp1,0,kb0),(0,kp2,0,kb0),(0,kp3,0,kb0),(0,kp4,0,kb0),(0,kp5,0,kb0),(0,kp6,0,kb0),(0,kp7,0,kb0),(0,kp8,0,kb0),(0,kp9,0,kb0),(0,kp10,0,kb0),(0,kp11,0,kb0),(0,kp12,0,kb0),(0,kp13,0,kb0),(0,kp14,0,kb0),(0,kp15,0,kb0),(0,kp16,0,kb0),(0,kp17,0,kb0),(0,kp18,0,kb0),(0,kp19,0,kb0),(0,kp20,0,kb0),(0,kp21,0,kb0),(0,kp22,0,kb0),(0,kp23,0,kb0),(0,kp24,0,kb0),(0,kp25,0,kb0),(0,kp26,0,kb0),(0,kp27,0,kb0),(0,kp28,0,kb0),(0,kp29,0,kb0),(0,kp30,0,kb0),(0,kp31,2,kb1),(0,kp32,5,kb1),(0,kp32,7,kb1),(0,kp31,10,kb1),(0,kp31,12,kb1),(0,kp31,15,kb2),(0,kp31,17,kb3),(0,kp31,19,kb3),(0,kp31,20,kb4),(0,kp33,0,kb0),(0,kp34,0,kb0),(0,kp35,0,kb0),(0,kp36,0,kb0),(0,kp37,0,kb0),(0,kp38,0,kb0),(0,kp39,0,kb0),(0,kp40,2,kb1),(0,kp40,10,kb1),(0,kp40,12,kb1),(0,kp40,15,kb2),(0,kp40,17,kb3),(0,kp40,19,kb3),(0,kp40,20,kb4),(0,kp41,0,kb0),(0,kp42,0,kb0),(0,kp43,0,kb0),(0,kp44,0,kb0),(0,kp45,0,kb0),(0,kp46,0,kb0),(0,kp47,0,kb0),(0,kp48,0,kb0),(0,kp49,0,kb0),(0,kp50,0,kb0),(0,kp51,0,kb0),(0,kp52,0,kb0),(0,kp53,0,kb0)]
private def pk1 : List CoverageKey := [(1,kp54,0,kb0),(1,kp55,0,kb0),(1,kp56,0,kb0),(1,kp57,0,kb0),(1,kp4,0,kb0),(1,kp5,0,kb0),(1,kp58,0,kb0),(1,kp59,0,kb0),(1,kp23,0,kb0),(1,kp24,0,kb0),(1,kp25,0,kb0),(1,kp26,0,kb0),(1,kp27,0,kb0),(1,kp28,0,kb0),(1,kp29,0,kb0),(1,kp30,0,kb0),(1,kp60,0,kb0),(1,kp61,0,kb0),(1,kp36,0,kb0),(1,kp37,0,kb0),(1,kp62,0,kb0),(1,kp42,0,kb0),(1,kp63,0,kb0),(1,kp64,0,kb0),(1,kp65,0,kb0),(1,kp66,2,kb1),(1,kp66,5,kb1),(1,kp66,7,kb1),(1,kp66,10,kb1),(1,kp66,12,kb3),(1,kp66,14,kb5),(1,kp66,17,kb3),(1,kp66,19,kb6),(1,kp66,20,kb4),(1,kp66,21,kb7),(1,kp67,0,kb0),(1,kp68,0,kb0),(1,kp69,0,kb0),(1,kp70,0,kb0),(1,kp71,0,kb0),(1,kp72,0,kb0),(1,kp73,0,kb0)]
private def pk2 : List CoverageKey := [(2,kp74,0,kb0),(2,kp75,0,kb0),(2,kp76,0,kb0),(2,kp77,0,kb0),(2,kp4,0,kb0),(2,kp5,0,kb0),(2,kp78,0,kb0),(2,kp79,0,kb0),(2,kp15,0,kb0),(2,kp16,0,kb0),(2,kp17,0,kb0),(2,kp18,0,kb0),(2,kp19,0,kb0),(2,kp20,0,kb0),(2,kp21,0,kb0),(2,kp22,0,kb0),(2,kp23,0,kb0),(2,kp24,0,kb0),(2,kp25,0,kb0),(2,kp26,0,kb0),(2,kp27,0,kb0),(2,kp28,0,kb0),(2,kp29,0,kb0),(2,kp30,0,kb0),(2,kp31,0,kb0),(2,kp80,0,kb0),(2,kp34,0,kb0),(2,kp35,0,kb0),(2,kp36,0,kb0),(2,kp37,0,kb0),(2,kp40,2,kb1),(2,kp40,5,kb1),(2,kp81,7,kb1),(2,kp40,10,kb1),(2,kp40,12,kb3),(2,kp40,14,kb5),(2,kp40,18,kb5),(2,kp40,20,kb5),(2,kp40,22,kb5),(2,kp40,24,kb5),(2,kp40,27,kb3),(2,kp40,29,kb6),(2,kp82,30,kb8),(2,kp40,31,kb9),(2,kp40,32,kb4),(2,kp83,2,kb1),(2,kp42,5,kb1),(2,kp42,10,kb1),(2,kp42,12,kb3),(2,kp42,14,kb5),(2,kp42,18,kb5),(2,kp42,20,kb5),(2,kp42,22,kb5),(2,kp42,24,kb5),(2,kp42,27,kb3),(2,kp42,29,kb6),(2,kp42,31,kb9),(2,kp42,32,kb4),(2,kp63,0,kb0),(2,kp64,0,kb0),(2,kp65,0,kb0),(2,kp46,0,kb0),(2,kp47,0,kb0),(2,kp84,0,kb0),(2,kp49,0,kb0),(2,kp66,5,kb1),(2,kp66,10,kb1),(2,kp66,12,kb3),(2,kp66,14,kb5),(2,kp66,18,kb5),(2,kp66,20,kb5),(2,kp66,22,kb5),(2,kp66,24,kb5),(2,kp66,27,kb3),(2,kp66,29,kb6),(2,kp66,30,kb8),(2,kp66,31,kb9),(2,kp85,32,kb4),(2,kp67,0,kb0),(2,kp68,0,kb0),(2,kp69,0,kb0),(2,kp50,0,kb0),(2,kp51,0,kb0),(2,kp86,0,kb0),(2,kp53,0,kb0),(2,kp70,5,kb1),(2,kp70,10,kb1),(2,kp70,12,kb3),(2,kp70,14,kb5),(2,kp70,18,kb5),(2,kp70,20,kb5),(2,kp70,22,kb5),(2,kp70,24,kb5),(2,kp70,27,kb3),(2,kp70,29,kb6),(2,kp70,31,kb9),(2,kp71,0,kb0),(2,kp72,0,kb0),(2,kp73,0,kb0)]
private def pk3 : List CoverageKey := [(3,kp54,0,kb0),(3,kp55,0,kb0),(3,kp56,0,kb0),(3,kp57,0,kb0),(3,kp87,0,kb0),(3,kp88,0,kb0),(3,kp58,0,kb0),(3,kp59,0,kb0),(3,kp23,0,kb0),(3,kp24,0,kb0),(3,kp25,0,kb0),(3,kp26,0,kb0),(3,kp27,0,kb0),(3,kp28,0,kb0),(3,kp29,0,kb0),(3,kp30,0,kb0),(3,kp60,0,kb0),(3,kp61,0,kb0),(3,kp36,0,kb0),(3,kp37,0,kb0),(3,kp62,0,kb0),(3,kp42,0,kb0),(3,kp63,0,kb0),(3,kp64,0,kb0),(3,kp65,0,kb0),(3,kp89,2,kb1),(3,kp66,5,kb1),(3,kp89,7,kb3),(3,kp66,9,kb3),(3,kp89,12,kb3),(3,kp66,14,kb5),(3,kp89,17,kb3),(3,kp66,19,kb3),(3,kp89,22,kb5),(3,kp66,24,kb3),(3,kp89,27,kb3),(3,kp66,29,kb5),(3,kp89,32,kb6),(3,kp66,34,kb1),(3,kp66,35,kb1),(3,kp66,36,kb2),(3,kp66,38,kb1),(3,kp66,39,kb2),(3,kp89,40,kb2),(3,kp66,41,kb4),(3,kp89,42,kb7),(3,kp67,5,kb1),(3,kp67,9,kb3),(3,kp67,14,kb5),(3,kp67,19,kb3),(3,kp67,24,kb3),(3,kp67,29,kb5),(3,kp67,34,kb1),(3,kp67,35,kb1),(3,kp67,36,kb2),(3,kp67,38,kb1),(3,kp67,39,kb2),(3,kp67,41,kb4),(3,kp68,0,kb0),(3,kp69,0,kb0),(3,kp70,0,kb0),(3,kp71,0,kb0),(3,kp72,0,kb0),(3,kp73,0,kb0)]
private def pk4 : List CoverageKey := [(4,kp90,0,kb0),(4,kp91,0,kb0),(4,kp56,0,kb0),(4,kp92,0,kb0),(4,kp87,0,kb0),(4,kp88,0,kb0),(4,kp58,0,kb0),(4,kp93,0,kb0),(4,kp19,0,kb0),(4,kp20,0,kb0),(4,kp21,0,kb0),(4,kp22,0,kb0),(4,kp23,0,kb0),(4,kp24,0,kb0),(4,kp25,0,kb0),(4,kp26,0,kb0),(4,kp27,0,kb0),(4,kp28,0,kb0),(4,kp29,0,kb0),(4,kp30,0,kb0),(4,kp94,0,kb0),(4,kp61,0,kb0),(4,kp35,0,kb0),(4,kp36,0,kb0),(4,kp37,0,kb0),(4,kp62,0,kb0),(4,kp42,0,kb0),(4,kp63,0,kb0),(4,kp64,0,kb0),(4,kp65,0,kb0),(4,kp66,2,kb1),(4,kp66,5,kb1),(4,kp66,7,kb3),(4,kp66,9,kb3),(4,kp66,12,kb3),(4,kp66,14,kb5),(4,kp66,17,kb3),(4,kp66,19,kb3),(4,kp66,22,kb5),(4,kp66,24,kb3),(4,kp66,27,kb3),(4,kp66,29,kb5),(4,kp66,33,kb5),(4,kp66,35,kb5),(4,kp66,37,kb5),(4,kp66,39,kb5),(4,kp66,42,kb6),(4,kp66,44,kb1),(4,kp66,45,kb1),(4,kp66,46,kb2),(4,kp66,48,kb1),(4,kp66,49,kb2),(4,kp66,50,kb2),(4,kp66,51,kb8),(4,kp66,52,kb9),(4,kp66,53,kb4),(4,kp67,0,kb0),(4,kp68,0,kb0),(4,kp69,0,kb0),(4,kp70,0,kb0),(4,kp71,0,kb0),(4,kp72,0,kb0),(4,kp73,0,kb0)]
private def pk5 : List CoverageKey := [(5,kp54,0,kb0),(5,kp55,0,kb0),(5,kp56,0,kb0),(5,kp57,0,kb0),(5,kp87,0,kb0),(5,kp88,0,kb0),(5,kp58,0,kb0),(5,kp59,0,kb0),(5,kp23,0,kb0),(5,kp24,0,kb0),(5,kp25,0,kb0),(5,kp26,0,kb0),(5,kp27,0,kb0),(5,kp28,0,kb0),(5,kp29,0,kb0),(5,kp30,0,kb0),(5,kp60,0,kb0),(5,kp61,0,kb0),(5,kp36,0,kb0),(5,kp37,0,kb0),(5,kp62,0,kb0),(5,kp95,0,kb0),(5,kp64,0,kb0),(5,kp65,0,kb0),(5,kp66,0,kb0),(5,kp67,2,kb1),(5,kp67,5,kb1),(5,kp67,7,kb3),(5,kp67,9,kb3),(5,kp67,12,kb1),(5,kp67,15,kb2),(5,kp67,17,kb3),(5,kp67,19,kb3),(5,kp67,22,kb5),(5,kp67,24,kb3),(5,kp67,27,kb3),(5,kp67,29,kb5),(5,kp67,32,kb6),(5,kp67,34,kb6),(5,kp67,35,kb6),(5,kp67,36,kb10),(5,kp67,38,kb1),(5,kp67,39,kb2),(5,kp67,40,kb2),(5,kp67,41,kb4),(5,kp67,42,kb7),(5,kp68,0,kb0),(5,kp69,0,kb0),(5,kp96,0,kb0),(5,kp72,0,kb0),(5,kp73,0,kb0)]
private def pk6 : List CoverageKey := [(6,kp54,0,kb0),(6,kp55,0,kb0),(6,kp56,0,kb0),(6,kp57,0,kb0),(6,kp87,0,kb0),(6,kp88,0,kb0),(6,kp58,0,kb0),(6,kp59,0,kb0),(6,kp23,0,kb0),(6,kp24,0,kb0),(6,kp25,0,kb0),(6,kp26,0,kb0),(6,kp27,0,kb0),(6,kp28,0,kb0),(6,kp29,0,kb0),(6,kp30,0,kb0),(6,kp60,0,kb0),(6,kp61,0,kb0),(6,kp36,0,kb0),(6,kp37,0,kb0),(6,kp62,0,kb0),(6,kp95,0,kb0),(6,kp64,0,kb0),(6,kp65,0,kb0),(6,kp89,0,kb0),(6,kp68,0,kb0),(6,kp69,0,kb0),(6,kp96,0,kb0),(6,kp72,0,kb0),(6,kp73,0,kb0)]
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
private abbrev specAt4 (pi goal : ℕ) : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 4) pi))[goal-1]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private abbrev cSpec4_0_1 := specAt4 0 1
private theorem cFlags4_0_1 : automaticFlags (trunkCatalog.states 4).context cSpec4_0_1 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_2 coordinateInput4_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_2 hCoordinate4_1]
  decide +kernel
private abbrev cSpec4_0_2 := specAt4 0 2
private theorem cFlags4_0_2 : automaticFlags (trunkCatalog.states 4).context cSpec4_0_2 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_4 coordinateInput4_5 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_4 hCoordinate4_5]
  decide +kernel
private abbrev cSpec4_0_3 := specAt4 0 3
private theorem cFlags4_0_3 : automaticFlags (trunkCatalog.states 4).context cSpec4_0_3 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_6 coordinateInput4_7 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_6 hCoordinate4_7]
  decide +kernel
private abbrev cSpec4_0_4 := specAt4 0 4
private theorem cFlags4_0_4 : automaticFlags (trunkCatalog.states 4).context cSpec4_0_4 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_8 coordinateInput4_9 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_8 hCoordinate4_9]
  decide +kernel
private abbrev cSpec4_0_5 := specAt4 0 5
private theorem cFlags4_0_5 : automaticFlags (trunkCatalog.states 4).context cSpec4_0_5 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_10 coordinateInput4_11 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_10 hCoordinate4_11]
  decide +kernel
private abbrev cSpec4_0_6 := specAt4 0 6
private theorem cFlags4_0_6 : automaticFlags (trunkCatalog.states 4).context cSpec4_0_6 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_0 coordinateInput4_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_0 hCoordinate4_3]
  decide +kernel
private abbrev cSpec4_0_7 := specAt4 0 7
private theorem cFlags4_0_7 : automaticFlags (trunkCatalog.states 4).context cSpec4_0_7 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_12 coordinateInput4_13 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_12 hCoordinate4_13]
  decide +kernel
private abbrev cSpec4_0_8 := specAt4 0 8
private theorem cFlags4_0_8 : automaticFlags (trunkCatalog.states 4).context cSpec4_0_8 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_14 coordinateInput4_15 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_14 hCoordinate4_15]
  decide +kernel
private abbrev cSpec4_0_9 := specAt4 0 9
private theorem cFlags4_0_9 : automaticFlags (trunkCatalog.states 4).context cSpec4_0_9 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_16 coordinateInput4_17 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_16 hCoordinate4_17]
  decide +kernel
private abbrev cSpec4_0_10 := specAt4 0 10
private theorem cFlags4_0_10 : automaticFlags (trunkCatalog.states 4).context cSpec4_0_10 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_18 coordinateInput4_19 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_18 hCoordinate4_19]
  decide +kernel
private abbrev cSpec4_0_11 := specAt4 0 11
private theorem cFlags4_0_11 : automaticFlags (trunkCatalog.states 4).context cSpec4_0_11 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_20 coordinateInput4_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_20 hCoordinate4_21]
  decide +kernel
private abbrev cSpec4_0_12 := specAt4 0 12
private theorem cFlags4_0_12 : automaticFlags (trunkCatalog.states 4).context cSpec4_0_12 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_22 coordinateInput4_23 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_22 hCoordinate4_23]
  decide +kernel
private abbrev cSpec4_0_13 := specAt4 0 13
private theorem cFlags4_0_13 : automaticFlags (trunkCatalog.states 4).context cSpec4_0_13 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_24 coordinateInput4_25 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_24 hCoordinate4_25]
  decide +kernel
private abbrev cSpec4_0_14 := specAt4 0 14
private theorem cFlags4_0_14 : automaticFlags (trunkCatalog.states 4).context cSpec4_0_14 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_26 coordinateInput4_27 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_26 hCoordinate4_27]
  decide +kernel
private abbrev cSpec4_0_15 := specAt4 0 15
private theorem cFlags4_0_15 : automaticFlags (trunkCatalog.states 4).context cSpec4_0_15 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_28 coordinateInput4_29 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_28 hCoordinate4_29]
  decide +kernel
private abbrev cSpec4_0_16 := specAt4 0 16
private theorem cFlags4_0_16 : automaticFlags (trunkCatalog.states 4).context cSpec4_0_16 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_2 coordinateInput4_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_2 hCoordinate4_3]
  decide +kernel
private abbrev cSpec4_0_17 := specAt4 0 17
private theorem cFlags4_0_17 : automaticFlags (trunkCatalog.states 4).context cSpec4_0_17 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_0 coordinateInput4_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_0 hCoordinate4_1]
  decide +kernel
private abbrev cSpec4_0_18 := specAt4 0 18
private theorem cFlags4_0_18 : automaticFlags (trunkCatalog.states 4).context cSpec4_0_18 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_0 coordinateInput4_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_0 hCoordinate4_21]
  decide +kernel
private abbrev cSpec4_0_19 := specAt4 0 19
private theorem cFlags4_0_19 : automaticFlags (trunkCatalog.states 4).context cSpec4_0_19 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_20 coordinateInput4_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_20 hCoordinate4_3]
  decide +kernel
private abbrev cSpec4_0_20 := specAt4 0 20
private theorem cFlags4_0_20 : automaticFlags (trunkCatalog.states 4).context cSpec4_0_20 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  rw [automaticFlags_cached _ _ coordinateInput4_2 coordinateInput4_30 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_2 hCoordinate4_30]
  decide +kernel
private abbrev cSpec4_0_21 := specAt4 0 21
private theorem cFlags4_0_21 : automaticFlags (trunkCatalog.states 4).context cSpec4_0_21 = (List.replicate 8 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_31 coordinateInput4_21 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_31 hCoordinate4_21]
  decide +kernel
private abbrev cSpec4_1_1 := specAt4 1 1
private theorem cFlags4_1_1 : automaticFlags (trunkCatalog.states 4).context cSpec4_1_1 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_1

private abbrev cSpec4_1_2 := specAt4 1 2
private theorem cFlags4_1_2 : automaticFlags (trunkCatalog.states 4).context cSpec4_1_2 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec4_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_2

private abbrev cSpec4_1_3 := specAt4 1 3
private theorem cFlags4_1_3 : automaticFlags (trunkCatalog.states 4).context cSpec4_1_3 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_3

private abbrev cSpec4_1_4 := specAt4 1 4
private theorem cFlags4_1_4 : automaticFlags (trunkCatalog.states 4).context cSpec4_1_4 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_4

private abbrev cSpec4_1_5 := specAt4 1 5
private theorem cFlags4_1_5 : automaticFlags (trunkCatalog.states 4).context cSpec4_1_5 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec4_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_5

private abbrev cSpec4_1_6 := specAt4 1 6
private theorem cFlags4_1_6 : automaticFlags (trunkCatalog.states 4).context cSpec4_1_6 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_6

private abbrev cSpec4_1_7 := specAt4 1 7
private theorem cFlags4_1_7 : automaticFlags (trunkCatalog.states 4).context cSpec4_1_7 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec4_0_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_7

private abbrev cSpec4_1_8 := specAt4 1 8
private theorem cFlags4_1_8 : automaticFlags (trunkCatalog.states 4).context cSpec4_1_8 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_8

private abbrev cSpec4_1_9 := specAt4 1 9
private theorem cFlags4_1_9 : automaticFlags (trunkCatalog.states 4).context cSpec4_1_9 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_9

private abbrev cSpec4_1_10 := specAt4 1 10
private theorem cFlags4_1_10 : automaticFlags (trunkCatalog.states 4).context cSpec4_1_10 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec4_0_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_10

private abbrev cSpec4_1_11 := specAt4 1 11
private theorem cFlags4_1_11 : automaticFlags (trunkCatalog.states 4).context cSpec4_1_11 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_32 coordinateInput4_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_32 hCoordinate4_33]
  decide +kernel
private abbrev cSpec4_1_12 := specAt4 1 12
private theorem cFlags4_1_12 : automaticFlags (trunkCatalog.states 4).context cSpec4_1_12 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_34 coordinateInput4_35 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_34 hCoordinate4_35]
  decide +kernel
private abbrev cSpec4_1_13 := specAt4 1 13
private theorem cFlags4_1_13 : automaticFlags (trunkCatalog.states 4).context cSpec4_1_13 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_36 coordinateInput4_37 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_36 hCoordinate4_37]
  decide +kernel
private abbrev cSpec4_1_14 := specAt4 1 14
private theorem cFlags4_1_14 : automaticFlags (trunkCatalog.states 4).context cSpec4_1_14 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_38 coordinateInput4_39 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_38 hCoordinate4_39]
  decide +kernel
private abbrev cSpec4_1_15 := specAt4 1 15
private theorem cFlags4_1_15 : automaticFlags (trunkCatalog.states 4).context cSpec4_1_15 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_40 coordinateInput4_41 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_40 hCoordinate4_41]
  decide +kernel
private abbrev cSpec4_1_16 := specAt4 1 16
private theorem cFlags4_1_16 : automaticFlags (trunkCatalog.states 4).context cSpec4_1_16 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_16

private abbrev cSpec4_1_17 := specAt4 1 17
private theorem cFlags4_1_17 : automaticFlags (trunkCatalog.states 4).context cSpec4_1_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_0_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_17

private abbrev cSpec4_1_18 := specAt4 1 18
private theorem cFlags4_1_18 : automaticFlags (trunkCatalog.states 4).context cSpec4_1_18 = (List.replicate 5 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_0 coordinateInput4_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_0 hCoordinate4_33]
  decide +kernel
private abbrev cSpec4_1_19 := specAt4 1 19
private theorem cFlags4_1_19 : automaticFlags (trunkCatalog.states 4).context cSpec4_1_19 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_32 coordinateInput4_3 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_32 hCoordinate4_3]
  decide +kernel
private abbrev cSpec4_1_20 := specAt4 1 20
private theorem cFlags4_1_20 : automaticFlags (trunkCatalog.states 4).context cSpec4_1_20 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  exact (automaticFlags_same _ _ cSpec4_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_20

private abbrev cSpec4_1_21 := specAt4 1 21
private theorem cFlags4_1_21 : automaticFlags (trunkCatalog.states 4).context cSpec4_1_21 = [false, true, false, false] := by
  rw [automaticFlags_cached _ _ coordinateInput4_31 coordinateInput4_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_31 hCoordinate4_33]
  decide +kernel
private abbrev cSpec4_2_1 := specAt4 2 1
private theorem cFlags4_2_1 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_1 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_1

private abbrev cSpec4_2_2 := specAt4 2 2
private theorem cFlags4_2_2 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_2 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec4_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_2

private abbrev cSpec4_2_3 := specAt4 2 3
private theorem cFlags4_2_3 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_3 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_3

private abbrev cSpec4_2_4 := specAt4 2 4
private theorem cFlags4_2_4 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_4 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_4

private abbrev cSpec4_2_5 := specAt4 2 5
private theorem cFlags4_2_5 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_5 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec4_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_5

private abbrev cSpec4_2_6 := specAt4 2 6
private theorem cFlags4_2_6 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_6 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_6

private abbrev cSpec4_2_7 := specAt4 2 7
private theorem cFlags4_2_7 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_7 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec4_0_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_7

private abbrev cSpec4_2_8 := specAt4 2 8
private theorem cFlags4_2_8 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_8 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_8

private abbrev cSpec4_2_9 := specAt4 2 9
private theorem cFlags4_2_9 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_9 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_9

private abbrev cSpec4_2_10 := specAt4 2 10
private theorem cFlags4_2_10 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_10 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec4_0_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_10

private abbrev cSpec4_2_11 := specAt4 2 11
private theorem cFlags4_2_11 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_11 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec4_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_11

private abbrev cSpec4_2_12 := specAt4 2 12
private theorem cFlags4_2_12 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_12 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_12

private abbrev cSpec4_2_13 := specAt4 2 13
private theorem cFlags4_2_13 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_13 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_13

private abbrev cSpec4_2_14 := specAt4 2 14
private theorem cFlags4_2_14 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_14 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec4_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_14

private abbrev cSpec4_2_15 := specAt4 2 15
private theorem cFlags4_2_15 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_15 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_15

private abbrev cSpec4_2_16 := specAt4 2 16
private theorem cFlags4_2_16 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_16 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_42 coordinateInput4_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_42 hCoordinate4_43]
  decide +kernel
private abbrev cSpec4_2_17 := specAt4 2 17
private theorem cFlags4_2_17 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_17 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_44 coordinateInput4_45 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_44 hCoordinate4_45]
  decide +kernel
private abbrev cSpec4_2_18 := specAt4 2 18
private theorem cFlags4_2_18 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_18 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_46 coordinateInput4_47 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_46 hCoordinate4_47]
  decide +kernel
private abbrev cSpec4_2_19 := specAt4 2 19
private theorem cFlags4_2_19 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_19 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_48 coordinateInput4_49 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_48 hCoordinate4_49]
  decide +kernel
private abbrev cSpec4_2_20 := specAt4 2 20
private theorem cFlags4_2_20 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_20 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_50 coordinateInput4_51 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_50 hCoordinate4_51]
  decide +kernel
private abbrev cSpec4_2_21 := specAt4 2 21
private theorem cFlags4_2_21 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_21 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_52 coordinateInput4_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_52 hCoordinate4_53]
  decide +kernel
private abbrev cSpec4_2_22 := specAt4 2 22
private theorem cFlags4_2_22 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_22 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_54 coordinateInput4_55 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_54 hCoordinate4_55]
  decide +kernel
private abbrev cSpec4_2_23 := specAt4 2 23
private theorem cFlags4_2_23 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_23 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_56 coordinateInput4_57 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_56 hCoordinate4_57]
  decide +kernel
private abbrev cSpec4_2_24 := specAt4 2 24
private theorem cFlags4_2_24 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_24 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_58 coordinateInput4_59 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_58 hCoordinate4_59]
  decide +kernel
private abbrev cSpec4_2_25 := specAt4 2 25
private theorem cFlags4_2_25 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_25 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_60 coordinateInput4_61 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_60 hCoordinate4_61]
  decide +kernel
private abbrev cSpec4_2_26 := specAt4 2 26
private theorem cFlags4_2_26 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_26 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_16

private abbrev cSpec4_2_27 := specAt4 2 27
private theorem cFlags4_2_27 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_0_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_17

private abbrev cSpec4_2_28 := specAt4 2 28
private theorem cFlags4_2_28 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_28 = (List.replicate 5 true) := by
  exact (automaticFlags_same _ _ cSpec4_1_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_18

private abbrev cSpec4_2_29 := specAt4 2 29
private theorem cFlags4_2_29 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_29 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec4_1_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_19

private abbrev cSpec4_2_30 := specAt4 2 30
private theorem cFlags4_2_30 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_30 = [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false] := by
  rw [automaticFlags_cached _ _ coordinateInput4_32 coordinateInput4_43 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_32 hCoordinate4_43]
  decide +kernel
private abbrev cSpec4_2_31 := specAt4 2 31
private theorem cFlags4_2_31 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_31 = (List.replicate 1 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_42 coordinateInput4_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_42 hCoordinate4_33]
  decide +kernel
private abbrev cSpec4_2_32 := specAt4 2 32
private theorem cFlags4_2_32 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_32 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  exact (automaticFlags_same _ _ cSpec4_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_20

private abbrev cSpec4_2_33 := specAt4 2 33
private theorem cFlags4_2_33 : automaticFlags (trunkCatalog.states 4).context cSpec4_2_33 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_31 coordinateInput4_53 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_31 hCoordinate4_53]
  decide +kernel
private abbrev cSpec4_3_1 := specAt4 3 1
private theorem cFlags4_3_1 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_1 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_1

private abbrev cSpec4_3_2 := specAt4 3 2
private theorem cFlags4_3_2 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_2 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec4_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_2

private abbrev cSpec4_3_3 := specAt4 3 3
private theorem cFlags4_3_3 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_3 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_3

private abbrev cSpec4_3_4 := specAt4 3 4
private theorem cFlags4_3_4 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_4 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_4

private abbrev cSpec4_3_5 := specAt4 3 5
private theorem cFlags4_3_5 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_5 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec4_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_5

private abbrev cSpec4_3_6 := specAt4 3 6
private theorem cFlags4_3_6 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_6 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_62 coordinateInput4_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_62 hCoordinate4_63]
  decide +kernel
private abbrev cSpec4_3_7 := specAt4 3 7
private theorem cFlags4_3_7 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_7 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_64 coordinateInput4_65 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_64 hCoordinate4_65]
  decide +kernel
private abbrev cSpec4_3_8 := specAt4 3 8
private theorem cFlags4_3_8 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_8 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_66 coordinateInput4_67 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_66 hCoordinate4_67]
  decide +kernel
private abbrev cSpec4_3_9 := specAt4 3 9
private theorem cFlags4_3_9 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_9 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_68 coordinateInput4_69 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_68 hCoordinate4_69]
  decide +kernel
private abbrev cSpec4_3_10 := specAt4 3 10
private theorem cFlags4_3_10 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_10 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_70 coordinateInput4_71 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_70 hCoordinate4_71]
  decide +kernel
private abbrev cSpec4_3_11 := specAt4 3 11
private theorem cFlags4_3_11 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_11 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_72 coordinateInput4_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_72 hCoordinate4_73]
  decide +kernel
private abbrev cSpec4_3_12 := specAt4 3 12
private theorem cFlags4_3_12 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_12 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_74 coordinateInput4_75 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_74 hCoordinate4_75]
  decide +kernel
private abbrev cSpec4_3_13 := specAt4 3 13
private theorem cFlags4_3_13 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_13 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_76 coordinateInput4_77 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_76 hCoordinate4_77]
  decide +kernel
private abbrev cSpec4_3_14 := specAt4 3 14
private theorem cFlags4_3_14 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_14 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_78 coordinateInput4_79 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_78 hCoordinate4_79]
  decide +kernel
private abbrev cSpec4_3_15 := specAt4 3 15
private theorem cFlags4_3_15 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_15 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_80 coordinateInput4_81 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_80 hCoordinate4_81]
  decide +kernel
private abbrev cSpec4_3_16 := specAt4 3 16
private theorem cFlags4_3_16 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_16 = (List.replicate 16 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_82 coordinateInput4_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_82 hCoordinate4_83]
  decide +kernel
private abbrev cSpec4_3_17 := specAt4 3 17
private theorem cFlags4_3_17 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_17 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_84 coordinateInput4_85 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_84 hCoordinate4_85]
  decide +kernel
private abbrev cSpec4_3_18 := specAt4 3 18
private theorem cFlags4_3_18 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_18 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_86 coordinateInput4_87 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_86 hCoordinate4_87]
  decide +kernel
private abbrev cSpec4_3_19 := specAt4 3 19
private theorem cFlags4_3_19 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_19 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_88 coordinateInput4_89 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_88 hCoordinate4_89]
  decide +kernel
private abbrev cSpec4_3_20 := specAt4 3 20
private theorem cFlags4_3_20 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_20 = (List.replicate 25 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_90 coordinateInput4_91 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_90 hCoordinate4_91]
  decide +kernel
private abbrev cSpec4_3_21 := specAt4 3 21
private theorem cFlags4_3_21 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_21 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_92 coordinateInput4_93 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_92 hCoordinate4_93]
  decide +kernel
private abbrev cSpec4_3_22 := specAt4 3 22
private theorem cFlags4_3_22 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_22 = (List.replicate 10 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_94 coordinateInput4_95 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_94 hCoordinate4_95]
  decide +kernel
private abbrev cSpec4_3_23 := specAt4 3 23
private theorem cFlags4_3_23 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_23 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_96 coordinateInput4_97 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_96 hCoordinate4_97]
  decide +kernel
private abbrev cSpec4_3_24 := specAt4 3 24
private theorem cFlags4_3_24 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_24 = (List.replicate 25 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_98 coordinateInput4_99 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_98 hCoordinate4_99]
  decide +kernel
private abbrev cSpec4_3_25 := specAt4 3 25
private theorem cFlags4_3_25 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_25 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_100 coordinateInput4_101 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_100 hCoordinate4_101]
  decide +kernel
private abbrev cSpec4_3_26 := specAt4 3 26
private theorem cFlags4_3_26 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec4_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_11

private abbrev cSpec4_3_27 := specAt4 3 27
private theorem cFlags4_3_27 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_12

private abbrev cSpec4_3_28 := specAt4 3 28
private theorem cFlags4_3_28 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_13

private abbrev cSpec4_3_29 := specAt4 3 29
private theorem cFlags4_3_29 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec4_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_14

private abbrev cSpec4_3_30 := specAt4 3 30
private theorem cFlags4_3_30 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_15

private abbrev cSpec4_3_31 := specAt4 3 31
private theorem cFlags4_3_31 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_31 = (List.replicate 20 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_2 coordinateInput4_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_2 hCoordinate4_63]
  decide +kernel
private abbrev cSpec4_3_32 := specAt4 3 32
private theorem cFlags4_3_32 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_32 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_62 coordinateInput4_1 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_62 hCoordinate4_1]
  decide +kernel
private abbrev cSpec4_3_33 := specAt4 3 33
private theorem cFlags4_3_33 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_33 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_62 coordinateInput4_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_62 hCoordinate4_73]
  decide +kernel
private abbrev cSpec4_3_34 := specAt4 3 34
private theorem cFlags4_3_34 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_34 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_72 coordinateInput4_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_72 hCoordinate4_63]
  decide +kernel
private abbrev cSpec4_3_35 := specAt4 3 35
private theorem cFlags4_3_35 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_35 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_72 coordinateInput4_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_72 hCoordinate4_83]
  decide +kernel
private abbrev cSpec4_3_36 := specAt4 3 36
private theorem cFlags4_3_36 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_36 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_82 coordinateInput4_73 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_82 hCoordinate4_73]
  decide +kernel
private abbrev cSpec4_3_37 := specAt4 3 37
private theorem cFlags4_3_37 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_37 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_82 coordinateInput4_93 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_82 hCoordinate4_93]
  decide +kernel
private abbrev cSpec4_3_38 := specAt4 3 38
private theorem cFlags4_3_38 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_38 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_92 coordinateInput4_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_92 hCoordinate4_83]
  decide +kernel
private abbrev cSpec4_3_39 := specAt4 3 39
private theorem cFlags4_3_39 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_39 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_92 coordinateInput4_33 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_92 hCoordinate4_33]
  decide +kernel
private abbrev cSpec4_3_40 := specAt4 3 40
private theorem cFlags4_3_40 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_40 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_32 coordinateInput4_93 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_32 hCoordinate4_93]
  decide +kernel
private abbrev cSpec4_3_41 := specAt4 3 41
private theorem cFlags4_3_41 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_41 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  exact (automaticFlags_same _ _ cSpec4_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_20

private abbrev cSpec4_3_42 := specAt4 3 42
private theorem cFlags4_3_42 : automaticFlags (trunkCatalog.states 4).context cSpec4_3_42 = [false, true, false, false] := by
  exact (automaticFlags_same _ _ cSpec4_1_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_21

private abbrev cSpec4_4_1 := specAt4 4 1
private theorem cFlags4_4_1 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_1 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_1

private abbrev cSpec4_4_2 := specAt4 4 2
private theorem cFlags4_4_2 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_2 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec4_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_2

private abbrev cSpec4_4_3 := specAt4 4 3
private theorem cFlags4_4_3 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_3 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_3

private abbrev cSpec4_4_4 := specAt4 4 4
private theorem cFlags4_4_4 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_4 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_4

private abbrev cSpec4_4_5 := specAt4 4 5
private theorem cFlags4_4_5 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_5 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec4_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_5

private abbrev cSpec4_4_6 := specAt4 4 6
private theorem cFlags4_4_6 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_6 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_6

private abbrev cSpec4_4_7 := specAt4 4 7
private theorem cFlags4_4_7 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_7 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_7

private abbrev cSpec4_4_8 := specAt4 4 8
private theorem cFlags4_4_8 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_8 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_8

private abbrev cSpec4_4_9 := specAt4 4 9
private theorem cFlags4_4_9 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_9 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_9

private abbrev cSpec4_4_10 := specAt4 4 10
private theorem cFlags4_4_10 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_10 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_10

private abbrev cSpec4_4_11 := specAt4 4 11
private theorem cFlags4_4_11 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_11 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_11

private abbrev cSpec4_4_12 := specAt4 4 12
private theorem cFlags4_4_12 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_12 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_12

private abbrev cSpec4_4_13 := specAt4 4 13
private theorem cFlags4_4_13 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_13 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_13

private abbrev cSpec4_4_14 := specAt4 4 14
private theorem cFlags4_4_14 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_14 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_14

private abbrev cSpec4_4_15 := specAt4 4 15
private theorem cFlags4_4_15 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_15 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_15

private abbrev cSpec4_4_16 := specAt4 4 16
private theorem cFlags4_4_16 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_16 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_16

private abbrev cSpec4_4_17 := specAt4 4 17
private theorem cFlags4_4_17 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_17

private abbrev cSpec4_4_18 := specAt4 4 18
private theorem cFlags4_4_18 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_18 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_18

private abbrev cSpec4_4_19 := specAt4 4 19
private theorem cFlags4_4_19 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_19 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_19

private abbrev cSpec4_4_20 := specAt4 4 20
private theorem cFlags4_4_20 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_20 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_20

private abbrev cSpec4_4_21 := specAt4 4 21
private theorem cFlags4_4_21 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_21 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_21

private abbrev cSpec4_4_22 := specAt4 4 22
private theorem cFlags4_4_22 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_22 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_22

private abbrev cSpec4_4_23 := specAt4 4 23
private theorem cFlags4_4_23 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_23 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_23

private abbrev cSpec4_4_24 := specAt4 4 24
private theorem cFlags4_4_24 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_24 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_24

private abbrev cSpec4_4_25 := specAt4 4 25
private theorem cFlags4_4_25 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_25 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_25

private abbrev cSpec4_4_26 := specAt4 4 26
private theorem cFlags4_4_26 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec4_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_11

private abbrev cSpec4_4_27 := specAt4 4 27
private theorem cFlags4_4_27 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_12

private abbrev cSpec4_4_28 := specAt4 4 28
private theorem cFlags4_4_28 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_13

private abbrev cSpec4_4_29 := specAt4 4 29
private theorem cFlags4_4_29 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec4_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_14

private abbrev cSpec4_4_30 := specAt4 4 30
private theorem cFlags4_4_30 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_15

private abbrev cSpec4_4_31 := specAt4 4 31
private theorem cFlags4_4_31 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_31 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec4_2_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_16

private abbrev cSpec4_4_32 := specAt4 4 32
private theorem cFlags4_4_32 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_32 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_2_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_17

private abbrev cSpec4_4_33 := specAt4 4 33
private theorem cFlags4_4_33 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_33 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec4_2_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_18

private abbrev cSpec4_4_34 := specAt4 4 34
private theorem cFlags4_4_34 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_34 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_2_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_19

private abbrev cSpec4_4_35 := specAt4 4 35
private theorem cFlags4_4_35 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_35 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec4_2_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_20

private abbrev cSpec4_4_36 := specAt4 4 36
private theorem cFlags4_4_36 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_36 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec4_2_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_21

private abbrev cSpec4_4_37 := specAt4 4 37
private theorem cFlags4_4_37 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_37 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec4_2_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_22

private abbrev cSpec4_4_38 := specAt4 4 38
private theorem cFlags4_4_38 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_38 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_2_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_23

private abbrev cSpec4_4_39 := specAt4 4 39
private theorem cFlags4_4_39 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_39 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec4_2_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_24

private abbrev cSpec4_4_40 := specAt4 4 40
private theorem cFlags4_4_40 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_40 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_2_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_25

private abbrev cSpec4_4_41 := specAt4 4 41
private theorem cFlags4_4_41 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_41 = (List.replicate 20 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_31

private abbrev cSpec4_4_42 := specAt4 4 42
private theorem cFlags4_4_42 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_42 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_32

private abbrev cSpec4_4_43 := specAt4 4 43
private theorem cFlags4_4_43 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_43 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_33 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_33

private abbrev cSpec4_4_44 := specAt4 4 44
private theorem cFlags4_4_44 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_44 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_34 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_34

private abbrev cSpec4_4_45 := specAt4 4 45
private theorem cFlags4_4_45 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_45 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_35 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_35

private abbrev cSpec4_4_46 := specAt4 4 46
private theorem cFlags4_4_46 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_46 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_36 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_36

private abbrev cSpec4_4_47 := specAt4 4 47
private theorem cFlags4_4_47 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_47 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_37 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_37

private abbrev cSpec4_4_48 := specAt4 4 48
private theorem cFlags4_4_48 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_48 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_38 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_38

private abbrev cSpec4_4_49 := specAt4 4 49
private theorem cFlags4_4_49 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_49 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_39 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_39

private abbrev cSpec4_4_50 := specAt4 4 50
private theorem cFlags4_4_50 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_50 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_40 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_40

private abbrev cSpec4_4_51 := specAt4 4 51
private theorem cFlags4_4_51 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_51 = [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false] := by
  exact (automaticFlags_same _ _ cSpec4_2_30 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_30

private abbrev cSpec4_4_52 := specAt4 4 52
private theorem cFlags4_4_52 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_52 = (List.replicate 1 false) := by
  exact (automaticFlags_same _ _ cSpec4_2_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_31

private abbrev cSpec4_4_53 := specAt4 4 53
private theorem cFlags4_4_53 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_53 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  exact (automaticFlags_same _ _ cSpec4_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_20

private abbrev cSpec4_4_54 := specAt4 4 54
private theorem cFlags4_4_54 : automaticFlags (trunkCatalog.states 4).context cSpec4_4_54 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec4_2_33 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_33

private abbrev cSpec4_5_1 := specAt4 5 1
private theorem cFlags4_5_1 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_1 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_1

private abbrev cSpec4_5_2 := specAt4 5 2
private theorem cFlags4_5_2 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_2 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec4_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_2

private abbrev cSpec4_5_3 := specAt4 5 3
private theorem cFlags4_5_3 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_3 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_3

private abbrev cSpec4_5_4 := specAt4 5 4
private theorem cFlags4_5_4 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_4 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_4

private abbrev cSpec4_5_5 := specAt4 5 5
private theorem cFlags4_5_5 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_5 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec4_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_5

private abbrev cSpec4_5_6 := specAt4 5 6
private theorem cFlags4_5_6 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_6 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_6

private abbrev cSpec4_5_7 := specAt4 5 7
private theorem cFlags4_5_7 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_7 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_7

private abbrev cSpec4_5_8 := specAt4 5 8
private theorem cFlags4_5_8 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_8 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_8

private abbrev cSpec4_5_9 := specAt4 5 9
private theorem cFlags4_5_9 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_9 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_9

private abbrev cSpec4_5_10 := specAt4 5 10
private theorem cFlags4_5_10 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_10 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_10

private abbrev cSpec4_5_11 := specAt4 5 11
private theorem cFlags4_5_11 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_11 = (List.replicate 10 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_102 coordinateInput4_103 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_102 hCoordinate4_103]
  decide +kernel
private abbrev cSpec4_5_12 := specAt4 5 12
private theorem cFlags4_5_12 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_12 = (List.replicate 16 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_104 coordinateInput4_105 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_104 hCoordinate4_105]
  decide +kernel
private abbrev cSpec4_5_13 := specAt4 5 13
private theorem cFlags4_5_13 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_13 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_106 coordinateInput4_107 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_106 hCoordinate4_107]
  decide +kernel
private abbrev cSpec4_5_14 := specAt4 5 14
private theorem cFlags4_5_14 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_14 = (List.replicate 4 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_108 coordinateInput4_109 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_108 hCoordinate4_109]
  decide +kernel
private abbrev cSpec4_5_15 := specAt4 5 15
private theorem cFlags4_5_15 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_15 = (List.replicate 4 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_110 coordinateInput4_111 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_110 hCoordinate4_111]
  decide +kernel
private abbrev cSpec4_5_16 := specAt4 5 16
private theorem cFlags4_5_16 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_16 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_16

private abbrev cSpec4_5_17 := specAt4 5 17
private theorem cFlags4_5_17 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_17

private abbrev cSpec4_5_18 := specAt4 5 18
private theorem cFlags4_5_18 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_18 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_18

private abbrev cSpec4_5_19 := specAt4 5 19
private theorem cFlags4_5_19 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_19 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_19

private abbrev cSpec4_5_20 := specAt4 5 20
private theorem cFlags4_5_20 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_20 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_20

private abbrev cSpec4_5_21 := specAt4 5 21
private theorem cFlags4_5_21 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_21 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_21

private abbrev cSpec4_5_22 := specAt4 5 22
private theorem cFlags4_5_22 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_22 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_22

private abbrev cSpec4_5_23 := specAt4 5 23
private theorem cFlags4_5_23 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_23 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_23

private abbrev cSpec4_5_24 := specAt4 5 24
private theorem cFlags4_5_24 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_24 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_24

private abbrev cSpec4_5_25 := specAt4 5 25
private theorem cFlags4_5_25 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_25 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_25

private abbrev cSpec4_5_26 := specAt4 5 26
private theorem cFlags4_5_26 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec4_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_11

private abbrev cSpec4_5_27 := specAt4 5 27
private theorem cFlags4_5_27 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_12

private abbrev cSpec4_5_28 := specAt4 5 28
private theorem cFlags4_5_28 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_13

private abbrev cSpec4_5_29 := specAt4 5 29
private theorem cFlags4_5_29 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec4_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_14

private abbrev cSpec4_5_30 := specAt4 5 30
private theorem cFlags4_5_30 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_15

private abbrev cSpec4_5_31 := specAt4 5 31
private theorem cFlags4_5_31 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_31 = (List.replicate 20 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_31

private abbrev cSpec4_5_32 := specAt4 5 32
private theorem cFlags4_5_32 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_32 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_32

private abbrev cSpec4_5_33 := specAt4 5 33
private theorem cFlags4_5_33 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_33 = (List.replicate 8 true) := by
  rw [automaticFlags_cached _ _ coordinateInput4_62 coordinateInput4_103 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_62 hCoordinate4_103]
  decide +kernel
private abbrev cSpec4_5_34 := specAt4 5 34
private theorem cFlags4_5_34 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_34 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_102 coordinateInput4_63 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_102 hCoordinate4_63]
  decide +kernel
private abbrev cSpec4_5_35 := specAt4 5 35
private theorem cFlags4_5_35 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_35 = (List.replicate 20 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_102 coordinateInput4_83 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_102 hCoordinate4_83]
  decide +kernel
private abbrev cSpec4_5_36 := specAt4 5 36
private theorem cFlags4_5_36 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_36 = (List.replicate 8 false) := by
  rw [automaticFlags_cached _ _ coordinateInput4_82 coordinateInput4_103 _ _
    (by decide +kernel) (by decide +kernel) hCoordinate4_82 hCoordinate4_103]
  decide +kernel
private abbrev cSpec4_5_37 := specAt4 5 37
private theorem cFlags4_5_37 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_37 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_37 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_37

private abbrev cSpec4_5_38 := specAt4 5 38
private theorem cFlags4_5_38 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_38 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_38 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_38

private abbrev cSpec4_5_39 := specAt4 5 39
private theorem cFlags4_5_39 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_39 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_39 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_39

private abbrev cSpec4_5_40 := specAt4 5 40
private theorem cFlags4_5_40 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_40 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_40 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_40

private abbrev cSpec4_5_41 := specAt4 5 41
private theorem cFlags4_5_41 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_41 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  exact (automaticFlags_same _ _ cSpec4_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_20

private abbrev cSpec4_5_42 := specAt4 5 42
private theorem cFlags4_5_42 : automaticFlags (trunkCatalog.states 4).context cSpec4_5_42 = [false, true, false, false] := by
  exact (automaticFlags_same _ _ cSpec4_1_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_21

private abbrev cSpec4_6_1 := specAt4 6 1
private theorem cFlags4_6_1 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_1 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_1

private abbrev cSpec4_6_2 := specAt4 6 2
private theorem cFlags4_6_2 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_2 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec4_0_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_2

private abbrev cSpec4_6_3 := specAt4 6 3
private theorem cFlags4_6_3 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_3 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_3

private abbrev cSpec4_6_4 := specAt4 6 4
private theorem cFlags4_6_4 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_4 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec4_0_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_4

private abbrev cSpec4_6_5 := specAt4 6 5
private theorem cFlags4_6_5 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_5 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec4_0_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_5

private abbrev cSpec4_6_6 := specAt4 6 6
private theorem cFlags4_6_6 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_6 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_6 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_6

private abbrev cSpec4_6_7 := specAt4 6 7
private theorem cFlags4_6_7 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_7 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_7

private abbrev cSpec4_6_8 := specAt4 6 8
private theorem cFlags4_6_8 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_8 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_8

private abbrev cSpec4_6_9 := specAt4 6 9
private theorem cFlags4_6_9 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_9 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_9 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_9

private abbrev cSpec4_6_10 := specAt4 6 10
private theorem cFlags4_6_10 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_10 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_10 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_10

private abbrev cSpec4_6_11 := specAt4 6 11
private theorem cFlags4_6_11 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_11 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_5_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_5_11

private abbrev cSpec4_6_12 := specAt4 6 12
private theorem cFlags4_6_12 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_12 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec4_5_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_5_12

private abbrev cSpec4_6_13 := specAt4 6 13
private theorem cFlags4_6_13 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_13 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec4_5_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_5_13

private abbrev cSpec4_6_14 := specAt4 6 14
private theorem cFlags4_6_14 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_14 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec4_5_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_5_14

private abbrev cSpec4_6_15 := specAt4 6 15
private theorem cFlags4_6_15 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_15 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec4_5_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_5_15

private abbrev cSpec4_6_16 := specAt4 6 16
private theorem cFlags4_6_16 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_16 = (List.replicate 16 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_16

private abbrev cSpec4_6_17 := specAt4 6 17
private theorem cFlags4_6_17 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_17 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_17

private abbrev cSpec4_6_18 := specAt4 6 18
private theorem cFlags4_6_18 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_18 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_18

private abbrev cSpec4_6_19 := specAt4 6 19
private theorem cFlags4_6_19 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_19 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_19

private abbrev cSpec4_6_20 := specAt4 6 20
private theorem cFlags4_6_20 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_20 = (List.replicate 25 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_20

private abbrev cSpec4_6_21 := specAt4 6 21
private theorem cFlags4_6_21 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_21 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_21

private abbrev cSpec4_6_22 := specAt4 6 22
private theorem cFlags4_6_22 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_22 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_22

private abbrev cSpec4_6_23 := specAt4 6 23
private theorem cFlags4_6_23 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_23 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_23

private abbrev cSpec4_6_24 := specAt4 6 24
private theorem cFlags4_6_24 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_24 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_24

private abbrev cSpec4_6_25 := specAt4 6 25
private theorem cFlags4_6_25 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_25 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_25

private abbrev cSpec4_6_26 := specAt4 6 26
private theorem cFlags4_6_26 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_26 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec4_1_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_11

private abbrev cSpec4_6_27 := specAt4 6 27
private theorem cFlags4_6_27 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_27 = (List.replicate 25 false) := by
  exact (automaticFlags_same _ _ cSpec4_1_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_12

private abbrev cSpec4_6_28 := specAt4 6 28
private theorem cFlags4_6_28 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_28 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_1_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_13

private abbrev cSpec4_6_29 := specAt4 6 29
private theorem cFlags4_6_29 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_29 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec4_1_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_14

private abbrev cSpec4_6_30 := specAt4 6 30
private theorem cFlags4_6_30 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_30 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_1_15 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_1_15

private abbrev cSpec4_6_31 := specAt4 6 31
private theorem cFlags4_6_31 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_31 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec4_2_16 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_16

private abbrev cSpec4_6_32 := specAt4 6 32
private theorem cFlags4_6_32 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_32 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_2_17 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_17

private abbrev cSpec4_6_33 := specAt4 6 33
private theorem cFlags4_6_33 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_33 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec4_2_18 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_18

private abbrev cSpec4_6_34 := specAt4 6 34
private theorem cFlags4_6_34 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_34 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_2_19 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_19

private abbrev cSpec4_6_35 := specAt4 6 35
private theorem cFlags4_6_35 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_35 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec4_2_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_20

private abbrev cSpec4_6_36 := specAt4 6 36
private theorem cFlags4_6_36 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_36 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec4_2_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_21

private abbrev cSpec4_6_37 := specAt4 6 37
private theorem cFlags4_6_37 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_37 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec4_2_22 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_22

private abbrev cSpec4_6_38 := specAt4 6 38
private theorem cFlags4_6_38 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_38 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_2_23 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_23

private abbrev cSpec4_6_39 := specAt4 6 39
private theorem cFlags4_6_39 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_39 = (List.replicate 10 false) := by
  exact (automaticFlags_same _ _ cSpec4_2_24 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_24

private abbrev cSpec4_6_40 := specAt4 6 40
private theorem cFlags4_6_40 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_40 = (List.replicate 10 true) := by
  exact (automaticFlags_same _ _ cSpec4_2_25 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_25

private abbrev cSpec4_6_41 := specAt4 6 41
private theorem cFlags4_6_41 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_41 = (List.replicate 20 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_31

private abbrev cSpec4_6_42 := specAt4 6 42
private theorem cFlags4_6_42 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_42 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_32

private abbrev cSpec4_6_43 := specAt4 6 43
private theorem cFlags4_6_43 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_43 = (List.replicate 8 true) := by
  exact (automaticFlags_same _ _ cSpec4_5_33 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_5_33

private abbrev cSpec4_6_44 := specAt4 6 44
private theorem cFlags4_6_44 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_44 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec4_5_34 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_5_34

private abbrev cSpec4_6_45 := specAt4 6 45
private theorem cFlags4_6_45 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_45 = (List.replicate 20 false) := by
  exact (automaticFlags_same _ _ cSpec4_5_35 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_5_35

private abbrev cSpec4_6_46 := specAt4 6 46
private theorem cFlags4_6_46 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_46 = (List.replicate 8 false) := by
  exact (automaticFlags_same _ _ cSpec4_5_36 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_5_36

private abbrev cSpec4_6_47 := specAt4 6 47
private theorem cFlags4_6_47 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_47 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec4_3_37 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_37

private abbrev cSpec4_6_48 := specAt4 6 48
private theorem cFlags4_6_48 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_48 = (List.replicate 16 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_38 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_38

private abbrev cSpec4_6_49 := specAt4 6 49
private theorem cFlags4_6_49 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_49 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_39 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_39

private abbrev cSpec4_6_50 := specAt4 6 50
private theorem cFlags4_6_50 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_50 = (List.replicate 4 false) := by
  exact (automaticFlags_same _ _ cSpec4_3_40 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_3_40

private abbrev cSpec4_6_51 := specAt4 6 51
private theorem cFlags4_6_51 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_51 = [true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false] := by
  exact (automaticFlags_same _ _ cSpec4_2_30 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_30

private abbrev cSpec4_6_52 := specAt4 6 52
private theorem cFlags4_6_52 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_52 = (List.replicate 1 false) := by
  exact (automaticFlags_same _ _ cSpec4_2_31 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_31

private abbrev cSpec4_6_53 := specAt4 6 53
private theorem cFlags4_6_53 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_53 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  exact (automaticFlags_same _ _ cSpec4_0_20 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_0_20

private abbrev cSpec4_6_54 := specAt4 6 54
private theorem cFlags4_6_54 : automaticFlags (trunkCatalog.states 4).context cSpec4_6_54 = (List.replicate 4 true) := by
  exact (automaticFlags_same _ _ cSpec4_2_33 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans cFlags4_2_33

private theorem keys_eq : coverageKeys (trunkCatalog.states 4) = checkedKeys := by
  rfl
private theorem tasks_eq : coverageTasks (trunkCatalog.states 4) = checkedTasks := by
  rw [← coverageTasksProjection_eq]
  change [(0,[(1, (automaticFlags (trunkCatalog.states 4).context cSpec4_0_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 4).context cSpec4_0_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 4).context cSpec4_0_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 4).context cSpec4_0_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 4).context cSpec4_0_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 4).context cSpec4_0_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 4).context cSpec4_0_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 4).context cSpec4_0_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 4).context cSpec4_0_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 4).context cSpec4_0_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 4).context cSpec4_0_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 4).context cSpec4_0_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 4).context cSpec4_0_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 4).context cSpec4_0_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 4).context cSpec4_0_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 4).context cSpec4_0_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 4).context cSpec4_0_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 4).context cSpec4_0_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 4).context cSpec4_0_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 4).context cSpec4_0_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 4).context cSpec4_0_21).zipIdx.map Prod.swap)]),(1,[(1, (automaticFlags (trunkCatalog.states 4).context cSpec4_1_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 4).context cSpec4_1_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 4).context cSpec4_1_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 4).context cSpec4_1_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 4).context cSpec4_1_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 4).context cSpec4_1_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 4).context cSpec4_1_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 4).context cSpec4_1_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 4).context cSpec4_1_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 4).context cSpec4_1_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 4).context cSpec4_1_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 4).context cSpec4_1_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 4).context cSpec4_1_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 4).context cSpec4_1_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 4).context cSpec4_1_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 4).context cSpec4_1_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 4).context cSpec4_1_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 4).context cSpec4_1_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 4).context cSpec4_1_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 4).context cSpec4_1_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 4).context cSpec4_1_21).zipIdx.map Prod.swap)]),(2,[(1, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 4).context cSpec4_2_33).zipIdx.map Prod.swap)]),(3,[(1, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 4).context cSpec4_3_42).zipIdx.map Prod.swap)]),(4,[(1, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_42).zipIdx.map Prod.swap),(43, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_43).zipIdx.map Prod.swap),(44, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_44).zipIdx.map Prod.swap),(45, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_45).zipIdx.map Prod.swap),(46, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_46).zipIdx.map Prod.swap),(47, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_47).zipIdx.map Prod.swap),(48, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_48).zipIdx.map Prod.swap),(49, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_49).zipIdx.map Prod.swap),(50, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_50).zipIdx.map Prod.swap),(51, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_51).zipIdx.map Prod.swap),(52, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_52).zipIdx.map Prod.swap),(53, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_53).zipIdx.map Prod.swap),(54, (automaticFlags (trunkCatalog.states 4).context cSpec4_4_54).zipIdx.map Prod.swap)]),(5,[(1, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 4).context cSpec4_5_42).zipIdx.map Prod.swap)]),(6,[(1, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_26).zipIdx.map Prod.swap),(27, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_27).zipIdx.map Prod.swap),(28, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_28).zipIdx.map Prod.swap),(29, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_29).zipIdx.map Prod.swap),(30, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_30).zipIdx.map Prod.swap),(31, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_31).zipIdx.map Prod.swap),(32, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_32).zipIdx.map Prod.swap),(33, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_33).zipIdx.map Prod.swap),(34, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_34).zipIdx.map Prod.swap),(35, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_35).zipIdx.map Prod.swap),(36, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_36).zipIdx.map Prod.swap),(37, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_37).zipIdx.map Prod.swap),(38, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_38).zipIdx.map Prod.swap),(39, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_39).zipIdx.map Prod.swap),(40, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_40).zipIdx.map Prod.swap),(41, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_41).zipIdx.map Prod.swap),(42, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_42).zipIdx.map Prod.swap),(43, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_43).zipIdx.map Prod.swap),(44, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_44).zipIdx.map Prod.swap),(45, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_45).zipIdx.map Prod.swap),(46, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_46).zipIdx.map Prod.swap),(47, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_47).zipIdx.map Prod.swap),(48, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_48).zipIdx.map Prod.swap),(49, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_49).zipIdx.map Prod.swap),(50, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_50).zipIdx.map Prod.swap),(51, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_51).zipIdx.map Prod.swap),(52, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_52).zipIdx.map Prod.swap),(53, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_53).zipIdx.map Prod.swap),(54, (automaticFlags (trunkCatalog.states 4).context cSpec4_6_54).zipIdx.map Prod.swap)])] = checkedTasks
  simp only [cFlags4_0_1, cFlags4_0_2, cFlags4_0_3, cFlags4_0_4, cFlags4_0_5, cFlags4_0_6, cFlags4_0_7, cFlags4_0_8, cFlags4_0_9, cFlags4_0_10, cFlags4_0_11, cFlags4_0_12, cFlags4_0_13, cFlags4_0_14, cFlags4_0_15, cFlags4_0_16, cFlags4_0_17, cFlags4_0_18, cFlags4_0_19, cFlags4_0_20, cFlags4_0_21, cFlags4_1_1, cFlags4_1_2, cFlags4_1_3, cFlags4_1_4, cFlags4_1_5, cFlags4_1_6, cFlags4_1_7, cFlags4_1_8, cFlags4_1_9, cFlags4_1_10, cFlags4_1_11, cFlags4_1_12, cFlags4_1_13, cFlags4_1_14, cFlags4_1_15, cFlags4_1_16, cFlags4_1_17, cFlags4_1_18, cFlags4_1_19, cFlags4_1_20, cFlags4_1_21, cFlags4_2_1, cFlags4_2_2, cFlags4_2_3, cFlags4_2_4, cFlags4_2_5, cFlags4_2_6, cFlags4_2_7, cFlags4_2_8, cFlags4_2_9, cFlags4_2_10, cFlags4_2_11, cFlags4_2_12, cFlags4_2_13, cFlags4_2_14, cFlags4_2_15, cFlags4_2_16, cFlags4_2_17, cFlags4_2_18, cFlags4_2_19, cFlags4_2_20, cFlags4_2_21, cFlags4_2_22, cFlags4_2_23, cFlags4_2_24, cFlags4_2_25, cFlags4_2_26, cFlags4_2_27, cFlags4_2_28, cFlags4_2_29, cFlags4_2_30, cFlags4_2_31, cFlags4_2_32, cFlags4_2_33, cFlags4_3_1, cFlags4_3_2, cFlags4_3_3, cFlags4_3_4, cFlags4_3_5, cFlags4_3_6, cFlags4_3_7, cFlags4_3_8, cFlags4_3_9, cFlags4_3_10, cFlags4_3_11, cFlags4_3_12, cFlags4_3_13, cFlags4_3_14, cFlags4_3_15, cFlags4_3_16, cFlags4_3_17, cFlags4_3_18, cFlags4_3_19, cFlags4_3_20, cFlags4_3_21, cFlags4_3_22, cFlags4_3_23, cFlags4_3_24, cFlags4_3_25, cFlags4_3_26, cFlags4_3_27, cFlags4_3_28, cFlags4_3_29, cFlags4_3_30, cFlags4_3_31, cFlags4_3_32, cFlags4_3_33, cFlags4_3_34, cFlags4_3_35, cFlags4_3_36, cFlags4_3_37, cFlags4_3_38, cFlags4_3_39, cFlags4_3_40, cFlags4_3_41, cFlags4_3_42, cFlags4_4_1, cFlags4_4_2, cFlags4_4_3, cFlags4_4_4, cFlags4_4_5, cFlags4_4_6, cFlags4_4_7, cFlags4_4_8, cFlags4_4_9, cFlags4_4_10, cFlags4_4_11, cFlags4_4_12, cFlags4_4_13, cFlags4_4_14, cFlags4_4_15, cFlags4_4_16, cFlags4_4_17, cFlags4_4_18, cFlags4_4_19, cFlags4_4_20, cFlags4_4_21, cFlags4_4_22, cFlags4_4_23, cFlags4_4_24, cFlags4_4_25, cFlags4_4_26, cFlags4_4_27, cFlags4_4_28, cFlags4_4_29, cFlags4_4_30, cFlags4_4_31, cFlags4_4_32, cFlags4_4_33, cFlags4_4_34, cFlags4_4_35, cFlags4_4_36, cFlags4_4_37, cFlags4_4_38, cFlags4_4_39, cFlags4_4_40, cFlags4_4_41, cFlags4_4_42, cFlags4_4_43, cFlags4_4_44, cFlags4_4_45, cFlags4_4_46, cFlags4_4_47, cFlags4_4_48, cFlags4_4_49, cFlags4_4_50, cFlags4_4_51, cFlags4_4_52, cFlags4_4_53, cFlags4_4_54, cFlags4_5_1, cFlags4_5_2, cFlags4_5_3, cFlags4_5_4, cFlags4_5_5, cFlags4_5_6, cFlags4_5_7, cFlags4_5_8, cFlags4_5_9, cFlags4_5_10, cFlags4_5_11, cFlags4_5_12, cFlags4_5_13, cFlags4_5_14, cFlags4_5_15, cFlags4_5_16, cFlags4_5_17, cFlags4_5_18, cFlags4_5_19, cFlags4_5_20, cFlags4_5_21, cFlags4_5_22, cFlags4_5_23, cFlags4_5_24, cFlags4_5_25, cFlags4_5_26, cFlags4_5_27, cFlags4_5_28, cFlags4_5_29, cFlags4_5_30, cFlags4_5_31, cFlags4_5_32, cFlags4_5_33, cFlags4_5_34, cFlags4_5_35, cFlags4_5_36, cFlags4_5_37, cFlags4_5_38, cFlags4_5_39, cFlags4_5_40, cFlags4_5_41, cFlags4_5_42, cFlags4_6_1, cFlags4_6_2, cFlags4_6_3, cFlags4_6_4, cFlags4_6_5, cFlags4_6_6, cFlags4_6_7, cFlags4_6_8, cFlags4_6_9, cFlags4_6_10, cFlags4_6_11, cFlags4_6_12, cFlags4_6_13, cFlags4_6_14, cFlags4_6_15, cFlags4_6_16, cFlags4_6_17, cFlags4_6_18, cFlags4_6_19, cFlags4_6_20, cFlags4_6_21, cFlags4_6_22, cFlags4_6_23, cFlags4_6_24, cFlags4_6_25, cFlags4_6_26, cFlags4_6_27, cFlags4_6_28, cFlags4_6_29, cFlags4_6_30, cFlags4_6_31, cFlags4_6_32, cFlags4_6_33, cFlags4_6_34, cFlags4_6_35, cFlags4_6_36, cFlags4_6_37, cFlags4_6_38, cFlags4_6_39, cFlags4_6_40, cFlags4_6_41, cFlags4_6_42, cFlags4_6_43, cFlags4_6_44, cFlags4_6_45, cFlags4_6_46, cFlags4_6_47, cFlags4_6_48, cFlags4_6_49, cFlags4_6_50, cFlags4_6_51, cFlags4_6_52, cFlags4_6_53, cFlags4_6_54]
  rfl
private theorem parents_length : (trunkRawParents (trunkCatalog.states 4).context).length = 625 := by
  decide +kernel
private theorem table_checked : coverageTable checkedKeys checkedTasks 625 := by
  apply coveragePlanRemainder_sound checkedPlanKeys _ _ [[179, 304], [484], [304, 359, 484, 609], [484, 489], [484], [489], []]
  unfold coveragePlanRemainder coverageRemainder parentsFor
  decide +kernel

theorem solution : trunkCoverage trunkCatalog 4 := by
  apply coverageTable_sound 4
  · unfold certRectangleValid; decide +kernel
  · decide +kernel
  · rw [keys_eq, tasks_eq, parents_length]
    exact table_checked
#print axioms solution
