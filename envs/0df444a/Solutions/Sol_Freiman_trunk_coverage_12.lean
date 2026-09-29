-- Prove2me | solution 1 for Freiman.trunk_coverage_12
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:14:17.609139+00:00
-- url     : https://prove2.me/submissions/613706b0-e926-4204-8920-53575b8f5344

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

private def coverageSorted (keys : List CoverageKey) (tasks : List CoverageTask) (parents : ℕ) : Prop :=
  ∀ pg ∈ tasks, ∀ gb ∈ pg.2, ∀ ba ∈ gb.2,
    ba.2 = true ∨ (List.range parents).Sublist
      (sortFuel 12 (parentsFor keys pg.1 0 (-1) ++ parentsFor keys pg.1 gb.1 ba.1))
private theorem coverageSorted_sound (keys : List CoverageKey) (tasks : List CoverageTask) (parents : ℕ)
    (h : coverageSorted keys tasks parents) : coverageTable keys tasks parents := by
  intro pg hpg par hpar
  by_cases he : coverageKeyRecorded keys pg.1 par 0 (-1)
  · exact Or.inl he
  · right
    intro gb hgb ba hba
    rcases h pg hpg gb hgb ba hba with ha | hs
    · exact Or.inl ha
    · right
      have hm := hs.subset hpar
      have hm' : par ∈ parentsFor keys pg.1 0 (-1) ++ parentsFor keys pg.1 gb.1 ba.1 := by
        simpa only [mem_sortFuel] using hm
      rcases List.mem_append.mp hm' with hx | hx
      · exact False.elim (he (parentsFor_sound _ _ _ _ _ hx))
      · exact parentsFor_sound _ _ _ _ _ hx
#print axioms coverageSorted_sound

open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false
private def coordinateFields12 : Array CertField := #[⟨(4/13),(1/13),(0/1),(0/1)⟩,⟨(1/2),(1/6),(0/1),(0/1)⟩,⟨(52/73),(1/73),(0/1),(0/1)⟩,⟨(89/214),(1/214),(0/1),(0/1)⟩,⟨(9/13),(-1/13),(0/1),(0/1)⟩,⟨(2/1),(-1/1),(0/1),(0/1)⟩,⟨(15/37),(-1/37),(0/1),(0/1)⟩,⟨(125/214),(-1/214),(0/1),(0/1)⟩,⟨(66/179),(-1/537),(0/1),(0/1)⟩,⟨(22/37),(1/37),(0/1),(0/1)⟩,⟨(113/179),(1/537),(0/1),(0/1)⟩,⟨(17/22),(-1/22),(0/1),(0/1)⟩,⟨(101/143),(-1/429),(0/1),(0/1)⟩,⟨(735/1006),(1/1006),(0/1),(0/1)⟩,⟨(35/94),(1/94),(0/1),(0/1)⟩,⟨(553/1429),(1/1429),(0/1),(0/1)⟩,⟨(10/23),(-1/69),(0/1),(0/1)⟩,⟨(517/1249),(-1/1249),(0/1),(0/1)⟩,⟨(1272/3013),(1/3013),(0/1),(0/1)⟩,⟨(5/22),(1/22),(0/1),(0/1)⟩,⟨(42/143),(1/429),(0/1),(0/1)⟩,⟨(271/1006),(-1/1006),(0/1),(0/1)⟩,⟨(16/59),(1/177),(0/1),(0/1)⟩,⟨(767/2749),(1/2749),(0/1),(0/1)⟩,⟨(43/142),(-1/142),(0/1),(0/1)⟩,⟨(731/2497),(-1/2497),(0/1),(0/1)⟩,⟨(1809/6094),(1/6094),(0/1),(0/1)⟩]
private abbrev coordinateInput12_0 : LowerPair × Bool × Bool := (([2], []), true, false)
private def coordinateCodes12_0 : List (ℕ × ℕ) := [(0, 1), (0, 1), (0, 2), (0, 1), (3, 1)]
private abbrev coordinateInput12_1 : LowerPair × Bool × Bool := (([1], []), false, false)
private def coordinateCodes12_1 : List (ℕ × ℕ) := [(4, 5), (4, 6), (4, 5), (7, 5), (4, 5)]
private abbrev coordinateInput12_2 : LowerPair × Bool × Bool := (([1], []), true, false)
private def coordinateCodes12_2 : List (ℕ × ℕ) := [(1, 1), (1, 1), (1, 2), (1, 1), (2, 1)]
private abbrev coordinateInput12_3 : LowerPair × Bool × Bool := (([2], []), false, false)
private def coordinateCodes12_3 : List (ℕ × ℕ) := [(6, 5), (6, 6), (6, 5), (8, 5), (6, 5)]
private abbrev coordinateInput12_4 : LowerPair × Bool × Bool := (([1, 1], []), true, false)
private def coordinateCodes12_4 : List (ℕ × ℕ) := [(9, 1), (9, 2), (9, 1), (10, 1)]
private abbrev coordinateInput12_5 : LowerPair × Bool × Bool := (([1, 2], []), false, false)
private def coordinateCodes12_5 : List (ℕ × ℕ) := [(11, 5), (11, 6), (11, 5), (12, 5)]
private abbrev coordinateInput12_6 : LowerPair × Bool × Bool := (([1, 2], []), true, false)
private def coordinateCodes12_6 : List (ℕ × ℕ) := [(2, 1), (2, 2), (2, 1), (13, 1)]
private abbrev coordinateInput12_7 : LowerPair × Bool × Bool := (([1, 1], []), false, false)
private def coordinateCodes12_7 : List (ℕ × ℕ) := [(4, 5), (4, 6), (4, 5), (7, 5)]
private abbrev coordinateInput12_8 : LowerPair × Bool × Bool := (([1], [1]), true, true)
private def coordinateCodes12_8 : List (ℕ × ℕ) := [(1, 1), (1, 2), (1, 1), (2, 1)]
private abbrev coordinateInput12_9 : LowerPair × Bool × Bool := (([1], [2]), false, true)
private def coordinateCodes12_9 : List (ℕ × ℕ) := [(4, 6), (4, 8), (4, 6), (7, 6)]
private abbrev coordinateInput12_10 : LowerPair × Bool × Bool := (([1], [2]), true, true)
private def coordinateCodes12_10 : List (ℕ × ℕ) := [(1, 0), (1, 3), (1, 0), (2, 0)]
private abbrev coordinateInput12_11 : LowerPair × Bool × Bool := (([1], [1]), false, true)
private def coordinateCodes12_11 : List (ℕ × ℕ) := [(4, 4), (4, 7), (4, 4), (7, 4)]
private abbrev coordinateInput12_12 : LowerPair × Bool × Bool := (([2, 1], []), true, false)
private def coordinateCodes12_12 : List (ℕ × ℕ) := [(14, 1), (14, 2), (14, 1), (15, 1)]
private abbrev coordinateInput12_13 : LowerPair × Bool × Bool := (([2, 2], []), false, false)
private def coordinateCodes12_13 : List (ℕ × ℕ) := [(16, 5), (16, 6), (16, 5), (17, 5)]
private abbrev coordinateInput12_14 : LowerPair × Bool × Bool := (([2, 2], []), true, false)
private def coordinateCodes12_14 : List (ℕ × ℕ) := [(3, 1), (3, 2), (3, 1), (18, 1)]
private abbrev coordinateInput12_15 : LowerPair × Bool × Bool := (([2, 1], []), false, false)
private def coordinateCodes12_15 : List (ℕ × ℕ) := [(6, 5), (6, 6), (6, 5), (8, 5)]
private abbrev coordinateInput12_16 : LowerPair × Bool × Bool := (([2], [1]), true, true)
private def coordinateCodes12_16 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 1), (3, 1)]
private abbrev coordinateInput12_17 : LowerPair × Bool × Bool := (([2], [2]), false, true)
private def coordinateCodes12_17 : List (ℕ × ℕ) := [(6, 6), (6, 8), (6, 6), (8, 6)]
private abbrev coordinateInput12_18 : LowerPair × Bool × Bool := (([2], [2]), true, true)
private def coordinateCodes12_18 : List (ℕ × ℕ) := [(0, 0), (0, 3), (0, 0), (3, 0)]
private abbrev coordinateInput12_19 : LowerPair × Bool × Bool := (([2], [1]), false, true)
private def coordinateCodes12_19 : List (ℕ × ℕ) := [(6, 4), (6, 7), (6, 4), (8, 4)]
private abbrev coordinateInput12_20 : LowerPair × Bool × Bool := (([], []), true, false)
private def coordinateCodes12_20 : List (ℕ × ℕ) := [(1, 1), (1, 2), (1, 1), (2, 1)]
private abbrev coordinateInput12_21 : LowerPair × Bool × Bool := (([], []), false, false)
private def coordinateCodes12_21 : List (ℕ × ℕ) := [(6, 5)]
private abbrev coordinateInput12_22 : LowerPair × Bool × Bool := (([2], [1]), true, false)
private def coordinateCodes12_22 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 1), (3, 1)]
private abbrev coordinateInput12_23 : LowerPair × Bool × Bool := (([2], [1]), false, false)
private def coordinateCodes12_23 : List (ℕ × ℕ) := [(6, 4), (6, 7), (6, 4), (8, 4)]
private abbrev coordinateInput12_24 : LowerPair × Bool × Bool := (([2, 1], [1]), true, false)
private def coordinateCodes12_24 : List (ℕ × ℕ) := [(14, 1), (14, 2), (14, 1), (15, 1), (14, 1)]
private abbrev coordinateInput12_25 : LowerPair × Bool × Bool := (([2, 2], [1]), false, false)
private def coordinateCodes12_25 : List (ℕ × ℕ) := [(16, 4), (16, 4), (16, 7), (16, 4), (17, 4)]
private abbrev coordinateInput12_26 : LowerPair × Bool × Bool := (([2, 2], [1]), true, false)
private def coordinateCodes12_26 : List (ℕ × ℕ) := [(3, 1), (3, 2), (3, 1), (18, 1), (3, 1)]
private abbrev coordinateInput12_27 : LowerPair × Bool × Bool := (([2, 1], [1]), false, false)
private def coordinateCodes12_27 : List (ℕ × ℕ) := [(6, 4), (6, 4), (6, 7), (6, 4), (8, 4)]
private abbrev coordinateInput12_28 : LowerPair × Bool × Bool := (([2], [1, 1]), true, true)
private def coordinateCodes12_28 : List (ℕ × ℕ) := [(0, 9), (0, 9), (0, 10), (0, 9), (3, 9)]
private abbrev coordinateInput12_29 : LowerPair × Bool × Bool := (([2], [1, 2]), false, true)
private def coordinateCodes12_29 : List (ℕ × ℕ) := [(6, 11), (6, 12), (6, 11), (8, 11), (6, 11)]
private abbrev coordinateInput12_30 : LowerPair × Bool × Bool := (([2], [1, 2]), true, true)
private def coordinateCodes12_30 : List (ℕ × ℕ) := [(0, 2), (0, 2), (0, 13), (0, 2), (3, 2)]
private abbrev coordinateInput12_31 : LowerPair × Bool × Bool := (([2], [1, 1]), false, true)
private def coordinateCodes12_31 : List (ℕ × ℕ) := [(6, 4), (6, 7), (6, 4), (8, 4), (6, 4)]
private abbrev coordinateInput12_32 : LowerPair × Bool × Bool := (([2], [2]), true, false)
private def coordinateCodes12_32 : List (ℕ × ℕ) := [(0, 0), (0, 3), (0, 0), (3, 0)]
private abbrev coordinateInput12_33 : LowerPair × Bool × Bool := (([2], [2]), false, false)
private def coordinateCodes12_33 : List (ℕ × ℕ) := [(6, 6), (6, 8), (6, 6), (8, 6)]
private abbrev coordinateInput12_34 : LowerPair × Bool × Bool := (([2, 1], [2]), true, false)
private def coordinateCodes12_34 : List (ℕ × ℕ) := [(14, 0), (14, 3), (14, 0), (15, 0), (14, 0)]
private abbrev coordinateInput12_35 : LowerPair × Bool × Bool := (([2, 2], [2]), false, false)
private def coordinateCodes12_35 : List (ℕ × ℕ) := [(16, 6), (16, 6), (16, 8), (16, 6), (17, 6)]
private abbrev coordinateInput12_36 : LowerPair × Bool × Bool := (([2, 2], [2]), true, false)
private def coordinateCodes12_36 : List (ℕ × ℕ) := [(3, 0), (3, 3), (3, 0), (18, 0), (3, 0)]
private abbrev coordinateInput12_37 : LowerPair × Bool × Bool := (([2, 1], [2]), false, false)
private def coordinateCodes12_37 : List (ℕ × ℕ) := [(6, 6), (6, 6), (6, 8), (6, 6), (8, 6)]
private abbrev coordinateInput12_38 : LowerPair × Bool × Bool := (([2], [2, 1]), true, true)
private def coordinateCodes12_38 : List (ℕ × ℕ) := [(0, 14), (0, 14), (0, 15), (0, 14), (3, 14)]
private abbrev coordinateInput12_39 : LowerPair × Bool × Bool := (([2], [2, 2]), false, true)
private def coordinateCodes12_39 : List (ℕ × ℕ) := [(6, 16), (6, 17), (6, 16), (8, 16), (6, 16)]
private abbrev coordinateInput12_40 : LowerPair × Bool × Bool := (([2], [2, 2]), true, true)
private def coordinateCodes12_40 : List (ℕ × ℕ) := [(0, 3), (0, 3), (0, 18), (0, 3), (3, 3)]
private abbrev coordinateInput12_41 : LowerPair × Bool × Bool := (([2], [2, 1]), false, true)
private def coordinateCodes12_41 : List (ℕ × ℕ) := [(6, 6), (6, 8), (6, 6), (8, 6), (6, 6)]
private abbrev coordinateInput12_42 : LowerPair × Bool × Bool := (([2], [3]), true, false)
private def coordinateCodes12_42 : List (ℕ × ℕ) := [(0, 19), (0, 20), (0, 19), (3, 19)]
private abbrev coordinateInput12_43 : LowerPair × Bool × Bool := (([2], [3]), false, false)
private def coordinateCodes12_43 : List (ℕ × ℕ) := [(6, 21)]
private abbrev coordinateInput12_44 : LowerPair × Bool × Bool := (([2, 1], [3]), true, false)
private def coordinateCodes12_44 : List (ℕ × ℕ) := [(14, 19), (14, 20), (14, 19), (15, 19), (14, 19)]
private abbrev coordinateInput12_45 : LowerPair × Bool × Bool := (([2, 2], [3]), false, false)
private def coordinateCodes12_45 : List (ℕ × ℕ) := [(16, 21), (16, 21)]
private abbrev coordinateInput12_46 : LowerPair × Bool × Bool := (([2, 2], [3]), true, false)
private def coordinateCodes12_46 : List (ℕ × ℕ) := [(3, 19), (3, 20), (3, 19), (18, 19), (3, 19)]
private abbrev coordinateInput12_47 : LowerPair × Bool × Bool := (([2, 1], [3]), false, false)
private def coordinateCodes12_47 : List (ℕ × ℕ) := [(6, 21), (6, 21)]
private abbrev coordinateInput12_48 : LowerPair × Bool × Bool := (([2], [3, 1]), true, true)
private def coordinateCodes12_48 : List (ℕ × ℕ) := [(0, 22), (0, 22), (0, 23), (0, 22), (3, 22)]
private abbrev coordinateInput12_49 : LowerPair × Bool × Bool := (([2], [3, 2]), false, true)
private def coordinateCodes12_49 : List (ℕ × ℕ) := [(6, 24), (6, 25), (6, 24), (8, 24), (6, 24)]
private abbrev coordinateInput12_50 : LowerPair × Bool × Bool := (([2], [3, 2]), true, true)
private def coordinateCodes12_50 : List (ℕ × ℕ) := [(0, 20), (0, 20), (0, 26), (0, 20), (3, 20)]
private abbrev coordinateInput12_51 : LowerPair × Bool × Bool := (([2], [3, 1]), false, true)
private def coordinateCodes12_51 : List (ℕ × ℕ) := [(6, 21), (6, 21)]

private def decodeCoordinate12 (x : ℕ × ℕ) : CertField × CertField :=
  (coordinateFields12[x.1]?.getD ⟨0,0,0,0⟩,coordinateFields12[x.2]?.getD ⟨0,0,0,0⟩)

private theorem hCoordinate12_0 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_0.1 coordinateInput12_0.2.1 coordinateInput12_0.2.2).map Prod.fst = coordinateCodes12_0.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_1 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_1.1 coordinateInput12_1.2.1 coordinateInput12_1.2.2).map Prod.fst = coordinateCodes12_1.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_2 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_2.1 coordinateInput12_2.2.1 coordinateInput12_2.2.2).map Prod.fst = coordinateCodes12_2.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_3 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_3.1 coordinateInput12_3.2.1 coordinateInput12_3.2.2).map Prod.fst = coordinateCodes12_3.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_4 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_4.1 coordinateInput12_4.2.1 coordinateInput12_4.2.2).map Prod.fst = coordinateCodes12_4.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_5 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_5.1 coordinateInput12_5.2.1 coordinateInput12_5.2.2).map Prod.fst = coordinateCodes12_5.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_6 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_6.1 coordinateInput12_6.2.1 coordinateInput12_6.2.2).map Prod.fst = coordinateCodes12_6.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_7 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_7.1 coordinateInput12_7.2.1 coordinateInput12_7.2.2).map Prod.fst = coordinateCodes12_7.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_8 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_8.1 coordinateInput12_8.2.1 coordinateInput12_8.2.2).map Prod.fst = coordinateCodes12_8.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_9 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_9.1 coordinateInput12_9.2.1 coordinateInput12_9.2.2).map Prod.fst = coordinateCodes12_9.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_10 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_10.1 coordinateInput12_10.2.1 coordinateInput12_10.2.2).map Prod.fst = coordinateCodes12_10.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_11 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_11.1 coordinateInput12_11.2.1 coordinateInput12_11.2.2).map Prod.fst = coordinateCodes12_11.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_12 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_12.1 coordinateInput12_12.2.1 coordinateInput12_12.2.2).map Prod.fst = coordinateCodes12_12.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_13 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_13.1 coordinateInput12_13.2.1 coordinateInput12_13.2.2).map Prod.fst = coordinateCodes12_13.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_14 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_14.1 coordinateInput12_14.2.1 coordinateInput12_14.2.2).map Prod.fst = coordinateCodes12_14.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_15 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_15.1 coordinateInput12_15.2.1 coordinateInput12_15.2.2).map Prod.fst = coordinateCodes12_15.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_16 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_16.1 coordinateInput12_16.2.1 coordinateInput12_16.2.2).map Prod.fst = coordinateCodes12_16.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_17 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_17.1 coordinateInput12_17.2.1 coordinateInput12_17.2.2).map Prod.fst = coordinateCodes12_17.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_18 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_18.1 coordinateInput12_18.2.1 coordinateInput12_18.2.2).map Prod.fst = coordinateCodes12_18.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_19 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_19.1 coordinateInput12_19.2.1 coordinateInput12_19.2.2).map Prod.fst = coordinateCodes12_19.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_20 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_20.1 coordinateInput12_20.2.1 coordinateInput12_20.2.2).map Prod.fst = coordinateCodes12_20.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_21 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_21.1 coordinateInput12_21.2.1 coordinateInput12_21.2.2).map Prod.fst = coordinateCodes12_21.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_22 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_22.1 coordinateInput12_22.2.1 coordinateInput12_22.2.2).map Prod.fst = coordinateCodes12_22.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_23 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_23.1 coordinateInput12_23.2.1 coordinateInput12_23.2.2).map Prod.fst = coordinateCodes12_23.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_24 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_24.1 coordinateInput12_24.2.1 coordinateInput12_24.2.2).map Prod.fst = coordinateCodes12_24.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_25 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_25.1 coordinateInput12_25.2.1 coordinateInput12_25.2.2).map Prod.fst = coordinateCodes12_25.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_26 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_26.1 coordinateInput12_26.2.1 coordinateInput12_26.2.2).map Prod.fst = coordinateCodes12_26.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_27 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_27.1 coordinateInput12_27.2.1 coordinateInput12_27.2.2).map Prod.fst = coordinateCodes12_27.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_28 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_28.1 coordinateInput12_28.2.1 coordinateInput12_28.2.2).map Prod.fst = coordinateCodes12_28.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_29 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_29.1 coordinateInput12_29.2.1 coordinateInput12_29.2.2).map Prod.fst = coordinateCodes12_29.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_30 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_30.1 coordinateInput12_30.2.1 coordinateInput12_30.2.2).map Prod.fst = coordinateCodes12_30.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_31 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_31.1 coordinateInput12_31.2.1 coordinateInput12_31.2.2).map Prod.fst = coordinateCodes12_31.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_32 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_32.1 coordinateInput12_32.2.1 coordinateInput12_32.2.2).map Prod.fst = coordinateCodes12_32.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_33 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_33.1 coordinateInput12_33.2.1 coordinateInput12_33.2.2).map Prod.fst = coordinateCodes12_33.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_34 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_34.1 coordinateInput12_34.2.1 coordinateInput12_34.2.2).map Prod.fst = coordinateCodes12_34.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_35 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_35.1 coordinateInput12_35.2.1 coordinateInput12_35.2.2).map Prod.fst = coordinateCodes12_35.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_36 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_36.1 coordinateInput12_36.2.1 coordinateInput12_36.2.2).map Prod.fst = coordinateCodes12_36.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_37 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_37.1 coordinateInput12_37.2.1 coordinateInput12_37.2.2).map Prod.fst = coordinateCodes12_37.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_38 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_38.1 coordinateInput12_38.2.1 coordinateInput12_38.2.2).map Prod.fst = coordinateCodes12_38.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_39 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_39.1 coordinateInput12_39.2.1 coordinateInput12_39.2.2).map Prod.fst = coordinateCodes12_39.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_40 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_40.1 coordinateInput12_40.2.1 coordinateInput12_40.2.2).map Prod.fst = coordinateCodes12_40.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_41 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_41.1 coordinateInput12_41.2.1 coordinateInput12_41.2.2).map Prod.fst = coordinateCodes12_41.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_42 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_42.1 coordinateInput12_42.2.1 coordinateInput12_42.2.2).map Prod.fst = coordinateCodes12_42.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_43 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_43.1 coordinateInput12_43.2.1 coordinateInput12_43.2.2).map Prod.fst = coordinateCodes12_43.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_44 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_44.1 coordinateInput12_44.2.1 coordinateInput12_44.2.2).map Prod.fst = coordinateCodes12_44.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_45 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_45.1 coordinateInput12_45.2.1 coordinateInput12_45.2.2).map Prod.fst = coordinateCodes12_45.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_46 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_46.1 coordinateInput12_46.2.1 coordinateInput12_46.2.2).map Prod.fst = coordinateCodes12_46.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_47 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_47.1 coordinateInput12_47.2.1 coordinateInput12_47.2.2).map Prod.fst = coordinateCodes12_47.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_48 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_48.1 coordinateInput12_48.2.1 coordinateInput12_48.2.2).map Prod.fst = coordinateCodes12_48.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_49 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_49.1 coordinateInput12_49.2.1 coordinateInput12_49.2.2).map Prod.fst = coordinateCodes12_49.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_50 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_50.1 coordinateInput12_50.2.1 coordinateInput12_50.2.2).map Prod.fst = coordinateCodes12_50.map decodeCoordinate12 := by decide +kernel

private theorem hCoordinate12_51 :
    (trunkEndpointCases (trunkCatalog.states 12).context coordinateInput12_51.1 coordinateInput12_51.2.1 coordinateInput12_51.2.2).map Prod.fst = coordinateCodes12_51.map decodeCoordinate12 := by decide +kernel

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

private def checkedKeys : List CoverageKey := [(0,[0,50],0,[-1]),
(0,[1,51],0,[-1]),
(0,[2,3,129],0,[-1]),
(0,[4,9,14,19,24,29,34,39,44,49,54,59,64,69,74,79,84,89,94,99,104,109,114,119,124,125,126,127,128,130,131,132,133,135,136,137,138,140,141,142,143,145,146,147,148,150,151,152,153,155,156,157,158,160,161,162,163,165,166,167,168,170,171,172,173,175,176,177,178,180,181,182,183,185,186,187,188,190,191,192,193,195,196,197,198,200,201,202,203,205,206,207,208,210,211,212,213,215,216,217,218,220,221,222,223,225,226,227,228,230,231,232,233,235,236,237,238,240,241,242,243,245,246,247,248,250,251,252,253,255,256,257,258,260,261,262,263,265,266,267,268,270,271,272,273,275,276,277,278,280,281,282,283,285,286,287,288,290,291,292,293,295,296,297,298,300,301,302,303,305,306,307,308,310,311,312,313,315,316,317,318,320,321,322,323,325,326,327,328,330,331,332,333,335,336,337,338,340,341,342,343,345,346,347,348,350,351,352,353,355,356,357,358,360,361,362,363,365,366,367,368,370,371,372,373,375,376,377,378,380,381,382,383,385,386,387,388,390,391,392,393,395,396,397,398,400,401,402,403,405,406,407,408,410,411,412,413,415,416,417,418,420,421,422,423,425,426,427,428,430,431,432,433,435,436,437,438,440,441,442,443,445,446,447,448,450,451,452,453,455,456,457,458,460,461,462,463,465,466,467,468,470,471,472,473,475,476,477,478,480,481,482,483,485,486,487,488,490,491,492,493,495,496,497,498,500,501,502,503,505,506,507,508,510,511,512,513,515,516,517,518,520,521,522,523,525,526,527,528,530,531,532,533,535,536,537,538,540,541,542,543,545,546,547,548,550,551,552,553,555,556,557,558,560,561,562,563,565,566,567,568,570,571,572,573,575,576,577,578,580,581,582,583,585,586,587,588,590,591,592,593,595,596,597,598,600,601,602,603,605,606,607,608,610,611,612,613,615,616,617,618,620,621,622,623],0,[-1]),
(0,[5,6,7,8,10,11,12,13,15,16,17,18,20,21,22,23,30,31,32,33,35,36,37,38,40,41,42,43,45,46,47,48,55,56,57,58,60,61,62,63,65,66,67,68,70,71,72,73,80,81,82,83,85,86,87,88,90,91,92,93,95,96,97,98,100,101,102,103,134,139,144,149,159,164,169,174,184,189,194,199,209,214,219,224,229,259,264,269,274,284,289,294,299,309,314,319,324,334,339,344,349,354,384,389,394,399,409,414,419,424,434,439,444,449,459,464,469,474,479,509,514,519,524,534,539,544,549,559,564,569,574,584,589,594,599,604],0,[-1]),
(0,[25],0,[-1]),
(0,[26],0,[-1]),
(0,[27,154],0,[-1]),
(0,[28],0,[-1]),
(0,[52],0,[-1]),
(0,[53],0,[-1]),
(0,[75],0,[-1]),
(0,[76],0,[-1]),
(0,[77],0,[-1]),
(0,[78],0,[-1]),
(0,[105],0,[-1]),
(0,[106],0,[-1]),
(0,[107],0,[-1]),
(0,[108],0,[-1]),
(0,[110],0,[-1]),
(0,[111],0,[-1]),
(0,[112],0,[-1]),
(0,[113],0,[-1]),
(0,[115],0,[-1]),
(0,[116],0,[-1]),
(0,[117],0,[-1]),
(0,[118],0,[-1]),
(0,[120],0,[-1]),
(0,[121],0,[-1]),
(0,[122],0,[-1]),
(0,[123],0,[-1]),
(0,[179],2,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[179,304],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[179,304,359],7,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[179],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[179],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(0,[179,304],13,[8,10,11,16,17,18]),
(0,[179,304,359],14,[1,3]),
(0,[204],0,[-1]),
(0,[234],0,[-1]),
(0,[239],0,[-1]),
(0,[244],0,[-1]),
(0,[249],0,[-1]),
(0,[254],0,[-1]),
(0,[279],0,[-1]),
(0,[304],2,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[304],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[304],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(0,[329],0,[-1]),
(0,[359],2,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[359],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[359],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[359],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(0,[359],13,[8,10,11,16,17,18]),
(0,[364,489,614],0,[-1]),
(0,[369,494,619],0,[-1]),
(0,[374,499,624],0,[-1]),
(0,[379],0,[-1]),
(0,[404],0,[-1]),
(0,[429],0,[-1]),
(0,[454],0,[-1]),
(0,[484],0,[-1]),
(0,[504],0,[-1]),
(0,[529],0,[-1]),
(0,[554],0,[-1]),
(0,[579],0,[-1]),
(0,[609],0,[-1]),
(1,[0,25,50,75,105],0,[-1]),
(1,[1,26,51,76,106],0,[-1]),
(1,[2,3,129,254],0,[-1]),
(1,[4,9,14,19,24,29,34,39,44,49,54,59,64,69,74,79,84,89,94,99,104,109,114,119,124,125,126,127,128,130,131,132,133,135,136,137,138,140,141,142,143,145,146,147,148,150,151,152,153,155,156,157,158,160,161,162,163,165,166,167,168,170,171,172,173,175,176,177,178,180,181,182,183,185,186,187,188,190,191,192,193,195,196,197,198,200,201,202,203,205,206,207,208,210,211,212,213,215,216,217,218,220,221,222,223,225,226,227,228,230,231,232,233,235,236,237,238,240,241,242,243,245,246,247,248,250,251,252,253,255,256,257,258,260,261,262,263,265,266,267,268,270,271,272,273,275,276,277,278,280,281,282,283,285,286,287,288,290,291,292,293,295,296,297,298,300,301,302,303,305,306,307,308,310,311,312,313,315,316,317,318,320,321,322,323,325,326,327,328,330,331,332,333,335,336,337,338,340,341,342,343,345,346,347,348,350,351,352,353,355,356,357,358,360,361,362,363,365,366,367,368,370,371,372,373,375,376,377,378,380,381,382,383,385,386,387,388,390,391,392,393,395,396,397,398,400,401,402,403,405,406,407,408,410,411,412,413,415,416,417,418,420,421,422,423,425,426,427,428,430,431,432,433,435,436,437,438,440,441,442,443,445,446,447,448,450,451,452,453,455,456,457,458,460,461,462,463,465,466,467,468,470,471,472,473,475,476,477,478,480,481,482,483,485,486,487,488,490,491,492,493,495,496,497,498,500,501,502,503,505,506,507,508,510,511,512,513,515,516,517,518,520,521,522,523,525,526,527,528,530,531,532,533,535,536,537,538,540,541,542,543,545,546,547,548,550,551,552,553,555,556,557,558,560,561,562,563,565,566,567,568,570,571,572,573,575,576,577,578,580,581,582,583,585,586,587,588,590,591,592,593,595,596,597,598,600,601,602,603,605,606,607,608,610,611,612,613,615,616,617,618,620,621,622,623],0,[-1]),
(1,[5,6,7,8,10,11,12,13,15,16,17,18,20,21,22,23,30,31,32,33,35,36,37,38,40,41,42,43,45,46,47,48,55,56,57,58,60,61,62,63,65,66,67,68,70,71,72,73,80,81,82,83,85,86,87,88,90,91,92,93,95,96,97,98,100,101,102,103,134,139,144,149,159,164,169,174,184,189,194,199,209,214,219,224,229,259,264,269,274,284,289,294,299,309,314,319,324,334,339,344,349,354,384,389,394,399,409,414,419,424,434,439,444,449,459,464,469,474,479,509,514,519,524,534,539,544,549,559,564,569,574,584,589,594,599,604],0,[-1]),
(1,[27,154,279],0,[-1]),
(1,[28,53,78,108],0,[-1]),
(1,[52,77,107],0,[-1]),
(1,[110],0,[-1]),
(1,[111],0,[-1]),
(1,[112],0,[-1]),
(1,[113],0,[-1]),
(1,[115],0,[-1]),
(1,[116],0,[-1]),
(1,[117],0,[-1]),
(1,[118],0,[-1]),
(1,[120],0,[-1]),
(1,[121],0,[-1]),
(1,[122],0,[-1]),
(1,[123],0,[-1]),
(1,[179,234],0,[-1]),
(1,[204,329],0,[-1]),
(1,[239],0,[-1]),
(1,[244],0,[-1]),
(1,[249],0,[-1]),
(1,[304],0,[-1]),
(1,[359,484,489,609],2,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(1,[359],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(1,[359,484,489,609],7,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(1,[359],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(1,[359],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(1,[359,484,609],13,[8,10,11,16,17,18]),
(1,[359,484,489,609],14,[1,3]),
(1,[364],0,[-1]),
(1,[369],0,[-1]),
(1,[374],0,[-1]),
(1,[379],0,[-1]),
(1,[404],0,[-1]),
(1,[429],0,[-1]),
(1,[454],0,[-1]),
(1,[484],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(1,[484],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(1,[484,489],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(1,[489],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(1,[489],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(1,[489],13,[8,10,11,16,17,18]),
(1,[494],0,[-1]),
(1,[499],0,[-1]),
(1,[504],0,[-1]),
(1,[529],0,[-1]),
(1,[554],0,[-1]),
(1,[579],0,[-1]),
(1,[609],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(1,[609],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(1,[609],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(1,[614],0,[-1]),
(1,[619],0,[-1]),
(1,[624],0,[-1]),
(2,[0,25,50,75,105,110],0,[-1]),
(2,[1,26,51,76,106,111],0,[-1]),
(2,[2,3,129,254,379,504],0,[-1]),
(2,[4,9,14,19,24,29,34,39,44,49,54,59,64,69,74,79,84,89,94,99,104,109,114,119,124,125,126,127,128,130,131,132,133,135,136,137,138,140,141,142,143,145,146,147,148,150,151,152,153,155,156,157,158,160,161,162,163,165,166,167,168,170,171,172,173,175,176,177,178,180,181,182,183,185,186,187,188,190,191,192,193,195,196,197,198,200,201,202,203,205,206,207,208,210,211,212,213,215,216,217,218,220,221,222,223,225,226,227,228,230,231,232,233,235,236,237,238,240,241,242,243,245,246,247,248,250,251,252,253,255,256,257,258,260,261,262,263,265,266,267,268,270,271,272,273,275,276,277,278,280,281,282,283,285,286,287,288,290,291,292,293,295,296,297,298,300,301,302,303,305,306,307,308,310,311,312,313,315,316,317,318,320,321,322,323,325,326,327,328,330,331,332,333,335,336,337,338,340,341,342,343,345,346,347,348,350,351,352,353,355,356,357,358,360,361,362,363,365,366,367,368,370,371,372,373,375,376,377,378,380,381,382,383,385,386,387,388,390,391,392,393,395,396,397,398,400,401,402,403,405,406,407,408,410,411,412,413,415,416,417,418,420,421,422,423,425,426,427,428,430,431,432,433,435,436,437,438,440,441,442,443,445,446,447,448,450,451,452,453,455,456,457,458,460,461,462,463,465,466,467,468,470,471,472,473,475,476,477,478,480,481,482,483,485,486,487,488,490,491,492,493,495,496,497,498,500,501,502,503,505,506,507,508,510,511,512,513,515,516,517,518,520,521,522,523,525,526,527,528,530,531,532,533,535,536,537,538,540,541,542,543,545,546,547,548,550,551,552,553,555,556,557,558,560,561,562,563,565,566,567,568,570,571,572,573,575,576,577,578,580,581,582,583,585,586,587,588,590,591,592,593,595,596,597,598,600,601,602,603,605,606,607,608,610,611,612,613,615,616,617,618,620,621,622,623],0,[-1]),
(2,[5,6,7,8,10,11,12,13,15,16,17,18,20,21,22,23,30,31,32,33,35,36,37,38,40,41,42,43,45,46,47,48,55,56,57,58,60,61,62,63,65,66,67,68,70,71,72,73,80,81,82,83,85,86,87,88,90,91,92,93,95,96,97,98,100,101,102,103,134,139,144,149,159,164,169,174,184,189,194,199,209,214,219,224,229,259,264,269,274,284,289,294,299,309,314,319,324,334,339,344,349,354,384,389,394,399,409,414,419,424,434,439,444,449,459,464,469,474,479,509,514,519,524,534,539,544,549,559,564,569,574,584,589,594,599,604],0,[-1]),
(2,[27,154,279,404,529],0,[-1]),
(2,[28,53,78,108,113],0,[-1]),
(2,[52,77,107,112],0,[-1]),
(2,[115],0,[-1]),
(2,[116],0,[-1]),
(2,[117],0,[-1]),
(2,[118],0,[-1]),
(2,[120],0,[-1]),
(2,[121],0,[-1]),
(2,[122],0,[-1]),
(2,[123],0,[-1]),
(2,[179,234,239],0,[-1]),
(2,[204,329,454,579],0,[-1]),
(2,[244],0,[-1]),
(2,[249],0,[-1]),
(2,[304,429,554],0,[-1]),
(2,[359,364],0,[-1]),
(2,[369],0,[-1]),
(2,[374],0,[-1]),
(2,[484,489,499],2,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[484],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[484,489,499],7,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[484],9,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[484,489],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[484],14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[484,489],17,[0,1,2,3,4,5,6,7,8,9]),
(2,[484],19,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[484,489,499],22,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]),
(2,[484],24,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[484],25,[8,10,11,16,17,18]),
(2,[489],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[489],9,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[489],14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[489],19,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[489],24,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[489],25,[8,10,11,16,17,18]),
(2,[494],0,[-1]),
(2,[499],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[499],9,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[499],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[499],14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[499],17,[0,1,2,3,4,5,6,7,8,9]),
(2,[499],19,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[499],24,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[499],25,[8,10,11,16,17,18]),
(2,[609,614],0,[-1]),
(2,[619],0,[-1]),
(2,[624],0,[-1])]
private def checkedTasks : List CoverageTask := [(0,[(1,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true),(16,true),(17,true),(18,true),(19,true),(20,true),(21,true),(22,true),(23,true),(24,true)]),(2,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false)]),(3,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true)]),(4,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true)]),(5,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false)]),(6,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true),(16,true),(17,true),(18,true),(19,true),(20,true),(21,true),(22,true),(23,true),(24,true)]),(7,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false)]),(8,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true)]),(9,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true)]),(10,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false)]),(11,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true),(16,true),(17,true),(18,true),(19,true),(20,true),(21,true),(22,true),(23,true),(24,true)]),(12,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false),(16,false),(17,false),(18,false),(19,false),(20,false),(21,false),(22,false),(23,false),(24,false)]),(13,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,false),(9,true),(10,false),(11,false),(12,true),(13,true),(14,true),(15,true),(16,false),(17,false),(18,false),(19,true)]),(14,[(0,true),(1,false),(2,true),(3,false),(4,true)])]),
(1,[(1,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true),(16,true),(17,true),(18,true),(19,true),(20,true),(21,true),(22,true),(23,true),(24,true)]),(2,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false)]),(3,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true)]),(4,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true)]),(5,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false)]),(6,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true),(16,true),(17,true),(18,true),(19,true),(20,true),(21,true),(22,true),(23,true),(24,true)]),(7,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false)]),(8,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true)]),(9,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true)]),(10,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false)]),(11,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true),(16,true),(17,true),(18,true),(19,true),(20,true),(21,true),(22,true),(23,true),(24,true)]),(12,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false),(16,false),(17,false),(18,false),(19,false),(20,false),(21,false),(22,false),(23,false),(24,false)]),(13,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,false),(9,true),(10,false),(11,false),(12,true),(13,true),(14,true),(15,true),(16,false),(17,false),(18,false),(19,true)]),(14,[(0,true),(1,false),(2,true),(3,false),(4,true)])]),
(2,[(1,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true),(16,true),(17,true),(18,true),(19,true),(20,true),(21,true),(22,true),(23,true),(24,true)]),(2,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false)]),(3,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true)]),(4,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true)]),(5,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false)]),(6,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true)]),(7,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false),(16,false),(17,false),(18,false),(19,false),(20,false),(21,false),(22,false),(23,false),(24,false)]),(8,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true),(16,true),(17,true),(18,true),(19,true),(20,true),(21,true),(22,true),(23,true),(24,true)]),(9,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false),(16,false),(17,false),(18,false),(19,false),(20,false),(21,false),(22,false),(23,false),(24,false)]),(10,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true),(16,true),(17,true),(18,true),(19,true),(20,true),(21,true),(22,true),(23,true),(24,true)]),(11,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true)]),(12,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false),(16,false),(17,false),(18,false),(19,false),(20,false),(21,false),(22,false),(23,false),(24,false)]),(13,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true),(16,true),(17,true),(18,true),(19,true),(20,true),(21,true),(22,true),(23,true),(24,true)]),(14,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false),(16,false),(17,false),(18,false),(19,false),(20,false),(21,false),(22,false),(23,false),(24,false)]),(15,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true),(16,true),(17,true),(18,true),(19,true),(20,true),(21,true),(22,true),(23,true),(24,true)]),(16,[(0,true),(1,true),(2,true),(3,true)]),(17,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false)]),(18,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true)]),(19,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false),(16,false),(17,false),(18,false),(19,false),(20,false),(21,false),(22,false),(23,false),(24,false)]),(20,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true)]),(21,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true),(16,true),(17,true),(18,true),(19,true)]),(22,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false),(16,false),(17,false),(18,false),(19,false)]),(23,[(0,true),(1,true),(2,true),(3,true)]),(24,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false)]),(25,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,false),(9,true),(10,false),(11,false),(12,true),(13,true),(14,true),(15,true),(16,false),(17,false),(18,false),(19,true)]),(26,[(0,true)])])]

private abbrev cSpec12_0_1 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 0))[0]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_0_1_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_1.first cSpec12_0_1.firstUpper (trunkSpecIncoming cSpec12_0_1)).map Prod.fst = coordinateCodes12_2.map decodeCoordinate12 := by
  have hi : (cSpec12_0_1.first, cSpec12_0_1.firstUpper, trunkSpecIncoming cSpec12_0_1) = coordinateInput12_2 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_2
private theorem cEq12_0_1_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_1.second cSpec12_0_1.secondUpper (trunkSpecIncoming cSpec12_0_1)).map Prod.fst = coordinateCodes12_1.map decodeCoordinate12 := by
  have hi : (cSpec12_0_1.second, cSpec12_0_1.secondUpper, trunkSpecIncoming cSpec12_0_1) = coordinateInput12_1 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_1
private theorem cFlags12_0_1 : automaticFlags (trunkCatalog.states 12).context cSpec12_0_1 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_0_1_first, cEq12_0_1_second]
  decide +kernel
private abbrev cSpec12_0_2 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 0))[1]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_0_2_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_2.first cSpec12_0_2.firstUpper (trunkSpecIncoming cSpec12_0_2)).map Prod.fst = coordinateCodes12_4.map decodeCoordinate12 := by
  have hi : (cSpec12_0_2.first, cSpec12_0_2.firstUpper, trunkSpecIncoming cSpec12_0_2) = coordinateInput12_4 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_4
private theorem cEq12_0_2_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_2.second cSpec12_0_2.secondUpper (trunkSpecIncoming cSpec12_0_2)).map Prod.fst = coordinateCodes12_5.map decodeCoordinate12 := by
  have hi : (cSpec12_0_2.second, cSpec12_0_2.secondUpper, trunkSpecIncoming cSpec12_0_2) = coordinateInput12_5 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_5
private theorem cFlags12_0_2 : automaticFlags (trunkCatalog.states 12).context cSpec12_0_2 = [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  unfold automaticFlags
  rw [cEq12_0_2_first, cEq12_0_2_second]
  decide +kernel
private abbrev cSpec12_0_3 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 0))[2]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_0_3_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_3.first cSpec12_0_3.firstUpper (trunkSpecIncoming cSpec12_0_3)).map Prod.fst = coordinateCodes12_6.map decodeCoordinate12 := by
  have hi : (cSpec12_0_3.first, cSpec12_0_3.firstUpper, trunkSpecIncoming cSpec12_0_3) = coordinateInput12_6 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_6
private theorem cEq12_0_3_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_3.second cSpec12_0_3.secondUpper (trunkSpecIncoming cSpec12_0_3)).map Prod.fst = coordinateCodes12_7.map decodeCoordinate12 := by
  have hi : (cSpec12_0_3.second, cSpec12_0_3.secondUpper, trunkSpecIncoming cSpec12_0_3) = coordinateInput12_7 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_7
private theorem cFlags12_0_3 : automaticFlags (trunkCatalog.states 12).context cSpec12_0_3 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_0_3_first, cEq12_0_3_second]
  decide +kernel
private abbrev cSpec12_0_4 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 0))[3]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_0_4_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_4.first cSpec12_0_4.firstUpper (trunkSpecIncoming cSpec12_0_4)).map Prod.fst = coordinateCodes12_8.map decodeCoordinate12 := by
  have hi : (cSpec12_0_4.first, cSpec12_0_4.firstUpper, trunkSpecIncoming cSpec12_0_4) = coordinateInput12_8 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_8
private theorem cEq12_0_4_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_4.second cSpec12_0_4.secondUpper (trunkSpecIncoming cSpec12_0_4)).map Prod.fst = coordinateCodes12_9.map decodeCoordinate12 := by
  have hi : (cSpec12_0_4.second, cSpec12_0_4.secondUpper, trunkSpecIncoming cSpec12_0_4) = coordinateInput12_9 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_9
private theorem cFlags12_0_4 : automaticFlags (trunkCatalog.states 12).context cSpec12_0_4 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_0_4_first, cEq12_0_4_second]
  decide +kernel
private abbrev cSpec12_0_5 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 0))[4]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_0_5_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_5.first cSpec12_0_5.firstUpper (trunkSpecIncoming cSpec12_0_5)).map Prod.fst = coordinateCodes12_10.map decodeCoordinate12 := by
  have hi : (cSpec12_0_5.first, cSpec12_0_5.firstUpper, trunkSpecIncoming cSpec12_0_5) = coordinateInput12_10 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_10
private theorem cEq12_0_5_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_5.second cSpec12_0_5.secondUpper (trunkSpecIncoming cSpec12_0_5)).map Prod.fst = coordinateCodes12_11.map decodeCoordinate12 := by
  have hi : (cSpec12_0_5.second, cSpec12_0_5.secondUpper, trunkSpecIncoming cSpec12_0_5) = coordinateInput12_11 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_11
private theorem cFlags12_0_5 : automaticFlags (trunkCatalog.states 12).context cSpec12_0_5 = [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  unfold automaticFlags
  rw [cEq12_0_5_first, cEq12_0_5_second]
  decide +kernel
private abbrev cSpec12_0_6 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 0))[5]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_0_6_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_6.first cSpec12_0_6.firstUpper (trunkSpecIncoming cSpec12_0_6)).map Prod.fst = coordinateCodes12_0.map decodeCoordinate12 := by
  have hi : (cSpec12_0_6.first, cSpec12_0_6.firstUpper, trunkSpecIncoming cSpec12_0_6) = coordinateInput12_0 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_0
private theorem cEq12_0_6_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_6.second cSpec12_0_6.secondUpper (trunkSpecIncoming cSpec12_0_6)).map Prod.fst = coordinateCodes12_3.map decodeCoordinate12 := by
  have hi : (cSpec12_0_6.second, cSpec12_0_6.secondUpper, trunkSpecIncoming cSpec12_0_6) = coordinateInput12_3 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_3
private theorem cFlags12_0_6 : automaticFlags (trunkCatalog.states 12).context cSpec12_0_6 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_0_6_first, cEq12_0_6_second]
  decide +kernel
private abbrev cSpec12_0_7 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 0))[6]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_0_7_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_7.first cSpec12_0_7.firstUpper (trunkSpecIncoming cSpec12_0_7)).map Prod.fst = coordinateCodes12_12.map decodeCoordinate12 := by
  have hi : (cSpec12_0_7.first, cSpec12_0_7.firstUpper, trunkSpecIncoming cSpec12_0_7) = coordinateInput12_12 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_12
private theorem cEq12_0_7_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_7.second cSpec12_0_7.secondUpper (trunkSpecIncoming cSpec12_0_7)).map Prod.fst = coordinateCodes12_13.map decodeCoordinate12 := by
  have hi : (cSpec12_0_7.second, cSpec12_0_7.secondUpper, trunkSpecIncoming cSpec12_0_7) = coordinateInput12_13 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_13
private theorem cFlags12_0_7 : automaticFlags (trunkCatalog.states 12).context cSpec12_0_7 = [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  unfold automaticFlags
  rw [cEq12_0_7_first, cEq12_0_7_second]
  decide +kernel
private abbrev cSpec12_0_8 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 0))[7]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_0_8_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_8.first cSpec12_0_8.firstUpper (trunkSpecIncoming cSpec12_0_8)).map Prod.fst = coordinateCodes12_14.map decodeCoordinate12 := by
  have hi : (cSpec12_0_8.first, cSpec12_0_8.firstUpper, trunkSpecIncoming cSpec12_0_8) = coordinateInput12_14 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_14
private theorem cEq12_0_8_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_8.second cSpec12_0_8.secondUpper (trunkSpecIncoming cSpec12_0_8)).map Prod.fst = coordinateCodes12_15.map decodeCoordinate12 := by
  have hi : (cSpec12_0_8.second, cSpec12_0_8.secondUpper, trunkSpecIncoming cSpec12_0_8) = coordinateInput12_15 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_15
private theorem cFlags12_0_8 : automaticFlags (trunkCatalog.states 12).context cSpec12_0_8 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_0_8_first, cEq12_0_8_second]
  decide +kernel
private abbrev cSpec12_0_9 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 0))[8]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_0_9_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_9.first cSpec12_0_9.firstUpper (trunkSpecIncoming cSpec12_0_9)).map Prod.fst = coordinateCodes12_16.map decodeCoordinate12 := by
  have hi : (cSpec12_0_9.first, cSpec12_0_9.firstUpper, trunkSpecIncoming cSpec12_0_9) = coordinateInput12_16 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_16
private theorem cEq12_0_9_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_9.second cSpec12_0_9.secondUpper (trunkSpecIncoming cSpec12_0_9)).map Prod.fst = coordinateCodes12_17.map decodeCoordinate12 := by
  have hi : (cSpec12_0_9.second, cSpec12_0_9.secondUpper, trunkSpecIncoming cSpec12_0_9) = coordinateInput12_17 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_17
private theorem cFlags12_0_9 : automaticFlags (trunkCatalog.states 12).context cSpec12_0_9 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_0_9_first, cEq12_0_9_second]
  decide +kernel
private abbrev cSpec12_0_10 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 0))[9]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_0_10_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_10.first cSpec12_0_10.firstUpper (trunkSpecIncoming cSpec12_0_10)).map Prod.fst = coordinateCodes12_18.map decodeCoordinate12 := by
  have hi : (cSpec12_0_10.first, cSpec12_0_10.firstUpper, trunkSpecIncoming cSpec12_0_10) = coordinateInput12_18 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_18
private theorem cEq12_0_10_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_10.second cSpec12_0_10.secondUpper (trunkSpecIncoming cSpec12_0_10)).map Prod.fst = coordinateCodes12_19.map decodeCoordinate12 := by
  have hi : (cSpec12_0_10.second, cSpec12_0_10.secondUpper, trunkSpecIncoming cSpec12_0_10) = coordinateInput12_19 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_19
private theorem cFlags12_0_10 : automaticFlags (trunkCatalog.states 12).context cSpec12_0_10 = [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  unfold automaticFlags
  rw [cEq12_0_10_first, cEq12_0_10_second]
  decide +kernel
private abbrev cSpec12_0_11 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 0))[10]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_0_11_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_11.first cSpec12_0_11.firstUpper (trunkSpecIncoming cSpec12_0_11)).map Prod.fst = coordinateCodes12_2.map decodeCoordinate12 := by
  have hi : (cSpec12_0_11.first, cSpec12_0_11.firstUpper, trunkSpecIncoming cSpec12_0_11) = coordinateInput12_2 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_2
private theorem cEq12_0_11_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_11.second cSpec12_0_11.secondUpper (trunkSpecIncoming cSpec12_0_11)).map Prod.fst = coordinateCodes12_3.map decodeCoordinate12 := by
  have hi : (cSpec12_0_11.second, cSpec12_0_11.secondUpper, trunkSpecIncoming cSpec12_0_11) = coordinateInput12_3 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_3
private theorem cFlags12_0_11 : automaticFlags (trunkCatalog.states 12).context cSpec12_0_11 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_0_11_first, cEq12_0_11_second]
  decide +kernel
private abbrev cSpec12_0_12 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 0))[11]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_0_12_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_12.first cSpec12_0_12.firstUpper (trunkSpecIncoming cSpec12_0_12)).map Prod.fst = coordinateCodes12_0.map decodeCoordinate12 := by
  have hi : (cSpec12_0_12.first, cSpec12_0_12.firstUpper, trunkSpecIncoming cSpec12_0_12) = coordinateInput12_0 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_0
private theorem cEq12_0_12_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_12.second cSpec12_0_12.secondUpper (trunkSpecIncoming cSpec12_0_12)).map Prod.fst = coordinateCodes12_1.map decodeCoordinate12 := by
  have hi : (cSpec12_0_12.second, cSpec12_0_12.secondUpper, trunkSpecIncoming cSpec12_0_12) = coordinateInput12_1 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_1
private theorem cFlags12_0_12 : automaticFlags (trunkCatalog.states 12).context cSpec12_0_12 = [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  unfold automaticFlags
  rw [cEq12_0_12_first, cEq12_0_12_second]
  decide +kernel
private abbrev cSpec12_0_13 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 0))[12]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_0_13_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_13.first cSpec12_0_13.firstUpper (trunkSpecIncoming cSpec12_0_13)).map Prod.fst = coordinateCodes12_2.map decodeCoordinate12 := by
  have hi : (cSpec12_0_13.first, cSpec12_0_13.firstUpper, trunkSpecIncoming cSpec12_0_13) = coordinateInput12_2 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_2
private theorem cEq12_0_13_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_13.second cSpec12_0_13.secondUpper (trunkSpecIncoming cSpec12_0_13)).map Prod.fst = coordinateCodes12_20.map decodeCoordinate12 := by
  have hi : (cSpec12_0_13.second, cSpec12_0_13.secondUpper, trunkSpecIncoming cSpec12_0_13) = coordinateInput12_20 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_20
private theorem cFlags12_0_13 : automaticFlags (trunkCatalog.states 12).context cSpec12_0_13 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  unfold automaticFlags
  rw [cEq12_0_13_first, cEq12_0_13_second]
  decide +kernel
private abbrev cSpec12_0_14 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 0))[13]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_0_14_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_14.first cSpec12_0_14.firstUpper (trunkSpecIncoming cSpec12_0_14)).map Prod.fst = coordinateCodes12_21.map decodeCoordinate12 := by
  have hi : (cSpec12_0_14.first, cSpec12_0_14.firstUpper, trunkSpecIncoming cSpec12_0_14) = coordinateInput12_21 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_21
private theorem cEq12_0_14_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_0_14.second cSpec12_0_14.secondUpper (trunkSpecIncoming cSpec12_0_14)).map Prod.fst = coordinateCodes12_3.map decodeCoordinate12 := by
  have hi : (cSpec12_0_14.second, cSpec12_0_14.secondUpper, trunkSpecIncoming cSpec12_0_14) = coordinateInput12_3 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_3
private theorem cFlags12_0_14 : automaticFlags (trunkCatalog.states 12).context cSpec12_0_14 = [true, false, true, false, true] := by
  unfold automaticFlags
  rw [cEq12_0_14_first, cEq12_0_14_second]
  decide +kernel
private abbrev cSpec12_1_1 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 1))[0]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_1_1_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_1.first cSpec12_1_1.firstUpper (trunkSpecIncoming cSpec12_1_1)).map Prod.fst = coordinateCodes12_2.map decodeCoordinate12 := by
  have hi : (cSpec12_1_1.first, cSpec12_1_1.firstUpper, trunkSpecIncoming cSpec12_1_1) = coordinateInput12_2 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_2
private theorem cEq12_1_1_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_1.second cSpec12_1_1.secondUpper (trunkSpecIncoming cSpec12_1_1)).map Prod.fst = coordinateCodes12_1.map decodeCoordinate12 := by
  have hi : (cSpec12_1_1.second, cSpec12_1_1.secondUpper, trunkSpecIncoming cSpec12_1_1) = coordinateInput12_1 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_1
private theorem cFlags12_1_1 : automaticFlags (trunkCatalog.states 12).context cSpec12_1_1 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_1_1_first, cEq12_1_1_second]
  decide +kernel
private abbrev cSpec12_1_2 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 1))[1]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_1_2_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_2.first cSpec12_1_2.firstUpper (trunkSpecIncoming cSpec12_1_2)).map Prod.fst = coordinateCodes12_4.map decodeCoordinate12 := by
  have hi : (cSpec12_1_2.first, cSpec12_1_2.firstUpper, trunkSpecIncoming cSpec12_1_2) = coordinateInput12_4 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_4
private theorem cEq12_1_2_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_2.second cSpec12_1_2.secondUpper (trunkSpecIncoming cSpec12_1_2)).map Prod.fst = coordinateCodes12_5.map decodeCoordinate12 := by
  have hi : (cSpec12_1_2.second, cSpec12_1_2.secondUpper, trunkSpecIncoming cSpec12_1_2) = coordinateInput12_5 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_5
private theorem cFlags12_1_2 : automaticFlags (trunkCatalog.states 12).context cSpec12_1_2 = [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  unfold automaticFlags
  rw [cEq12_1_2_first, cEq12_1_2_second]
  decide +kernel
private abbrev cSpec12_1_3 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 1))[2]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_1_3_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_3.first cSpec12_1_3.firstUpper (trunkSpecIncoming cSpec12_1_3)).map Prod.fst = coordinateCodes12_6.map decodeCoordinate12 := by
  have hi : (cSpec12_1_3.first, cSpec12_1_3.firstUpper, trunkSpecIncoming cSpec12_1_3) = coordinateInput12_6 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_6
private theorem cEq12_1_3_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_3.second cSpec12_1_3.secondUpper (trunkSpecIncoming cSpec12_1_3)).map Prod.fst = coordinateCodes12_7.map decodeCoordinate12 := by
  have hi : (cSpec12_1_3.second, cSpec12_1_3.secondUpper, trunkSpecIncoming cSpec12_1_3) = coordinateInput12_7 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_7
private theorem cFlags12_1_3 : automaticFlags (trunkCatalog.states 12).context cSpec12_1_3 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_1_3_first, cEq12_1_3_second]
  decide +kernel
private abbrev cSpec12_1_4 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 1))[3]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_1_4_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_4.first cSpec12_1_4.firstUpper (trunkSpecIncoming cSpec12_1_4)).map Prod.fst = coordinateCodes12_8.map decodeCoordinate12 := by
  have hi : (cSpec12_1_4.first, cSpec12_1_4.firstUpper, trunkSpecIncoming cSpec12_1_4) = coordinateInput12_8 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_8
private theorem cEq12_1_4_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_4.second cSpec12_1_4.secondUpper (trunkSpecIncoming cSpec12_1_4)).map Prod.fst = coordinateCodes12_9.map decodeCoordinate12 := by
  have hi : (cSpec12_1_4.second, cSpec12_1_4.secondUpper, trunkSpecIncoming cSpec12_1_4) = coordinateInput12_9 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_9
private theorem cFlags12_1_4 : automaticFlags (trunkCatalog.states 12).context cSpec12_1_4 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_1_4_first, cEq12_1_4_second]
  decide +kernel
private abbrev cSpec12_1_5 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 1))[4]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_1_5_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_5.first cSpec12_1_5.firstUpper (trunkSpecIncoming cSpec12_1_5)).map Prod.fst = coordinateCodes12_10.map decodeCoordinate12 := by
  have hi : (cSpec12_1_5.first, cSpec12_1_5.firstUpper, trunkSpecIncoming cSpec12_1_5) = coordinateInput12_10 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_10
private theorem cEq12_1_5_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_5.second cSpec12_1_5.secondUpper (trunkSpecIncoming cSpec12_1_5)).map Prod.fst = coordinateCodes12_11.map decodeCoordinate12 := by
  have hi : (cSpec12_1_5.second, cSpec12_1_5.secondUpper, trunkSpecIncoming cSpec12_1_5) = coordinateInput12_11 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_11
private theorem cFlags12_1_5 : automaticFlags (trunkCatalog.states 12).context cSpec12_1_5 = [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  unfold automaticFlags
  rw [cEq12_1_5_first, cEq12_1_5_second]
  decide +kernel
private abbrev cSpec12_1_6 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 1))[5]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_1_6_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_6.first cSpec12_1_6.firstUpper (trunkSpecIncoming cSpec12_1_6)).map Prod.fst = coordinateCodes12_0.map decodeCoordinate12 := by
  have hi : (cSpec12_1_6.first, cSpec12_1_6.firstUpper, trunkSpecIncoming cSpec12_1_6) = coordinateInput12_0 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_0
private theorem cEq12_1_6_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_6.second cSpec12_1_6.secondUpper (trunkSpecIncoming cSpec12_1_6)).map Prod.fst = coordinateCodes12_3.map decodeCoordinate12 := by
  have hi : (cSpec12_1_6.second, cSpec12_1_6.secondUpper, trunkSpecIncoming cSpec12_1_6) = coordinateInput12_3 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_3
private theorem cFlags12_1_6 : automaticFlags (trunkCatalog.states 12).context cSpec12_1_6 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_1_6_first, cEq12_1_6_second]
  decide +kernel
private abbrev cSpec12_1_7 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 1))[6]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_1_7_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_7.first cSpec12_1_7.firstUpper (trunkSpecIncoming cSpec12_1_7)).map Prod.fst = coordinateCodes12_12.map decodeCoordinate12 := by
  have hi : (cSpec12_1_7.first, cSpec12_1_7.firstUpper, trunkSpecIncoming cSpec12_1_7) = coordinateInput12_12 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_12
private theorem cEq12_1_7_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_7.second cSpec12_1_7.secondUpper (trunkSpecIncoming cSpec12_1_7)).map Prod.fst = coordinateCodes12_13.map decodeCoordinate12 := by
  have hi : (cSpec12_1_7.second, cSpec12_1_7.secondUpper, trunkSpecIncoming cSpec12_1_7) = coordinateInput12_13 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_13
private theorem cFlags12_1_7 : automaticFlags (trunkCatalog.states 12).context cSpec12_1_7 = [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  unfold automaticFlags
  rw [cEq12_1_7_first, cEq12_1_7_second]
  decide +kernel
private abbrev cSpec12_1_8 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 1))[7]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_1_8_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_8.first cSpec12_1_8.firstUpper (trunkSpecIncoming cSpec12_1_8)).map Prod.fst = coordinateCodes12_14.map decodeCoordinate12 := by
  have hi : (cSpec12_1_8.first, cSpec12_1_8.firstUpper, trunkSpecIncoming cSpec12_1_8) = coordinateInput12_14 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_14
private theorem cEq12_1_8_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_8.second cSpec12_1_8.secondUpper (trunkSpecIncoming cSpec12_1_8)).map Prod.fst = coordinateCodes12_15.map decodeCoordinate12 := by
  have hi : (cSpec12_1_8.second, cSpec12_1_8.secondUpper, trunkSpecIncoming cSpec12_1_8) = coordinateInput12_15 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_15
private theorem cFlags12_1_8 : automaticFlags (trunkCatalog.states 12).context cSpec12_1_8 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_1_8_first, cEq12_1_8_second]
  decide +kernel
private abbrev cSpec12_1_9 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 1))[8]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_1_9_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_9.first cSpec12_1_9.firstUpper (trunkSpecIncoming cSpec12_1_9)).map Prod.fst = coordinateCodes12_16.map decodeCoordinate12 := by
  have hi : (cSpec12_1_9.first, cSpec12_1_9.firstUpper, trunkSpecIncoming cSpec12_1_9) = coordinateInput12_16 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_16
private theorem cEq12_1_9_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_9.second cSpec12_1_9.secondUpper (trunkSpecIncoming cSpec12_1_9)).map Prod.fst = coordinateCodes12_17.map decodeCoordinate12 := by
  have hi : (cSpec12_1_9.second, cSpec12_1_9.secondUpper, trunkSpecIncoming cSpec12_1_9) = coordinateInput12_17 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_17
private theorem cFlags12_1_9 : automaticFlags (trunkCatalog.states 12).context cSpec12_1_9 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_1_9_first, cEq12_1_9_second]
  decide +kernel
private abbrev cSpec12_1_10 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 1))[9]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_1_10_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_10.first cSpec12_1_10.firstUpper (trunkSpecIncoming cSpec12_1_10)).map Prod.fst = coordinateCodes12_18.map decodeCoordinate12 := by
  have hi : (cSpec12_1_10.first, cSpec12_1_10.firstUpper, trunkSpecIncoming cSpec12_1_10) = coordinateInput12_18 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_18
private theorem cEq12_1_10_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_10.second cSpec12_1_10.secondUpper (trunkSpecIncoming cSpec12_1_10)).map Prod.fst = coordinateCodes12_19.map decodeCoordinate12 := by
  have hi : (cSpec12_1_10.second, cSpec12_1_10.secondUpper, trunkSpecIncoming cSpec12_1_10) = coordinateInput12_19 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_19
private theorem cFlags12_1_10 : automaticFlags (trunkCatalog.states 12).context cSpec12_1_10 = [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  unfold automaticFlags
  rw [cEq12_1_10_first, cEq12_1_10_second]
  decide +kernel
private abbrev cSpec12_1_11 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 1))[10]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_1_11_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_11.first cSpec12_1_11.firstUpper (trunkSpecIncoming cSpec12_1_11)).map Prod.fst = coordinateCodes12_2.map decodeCoordinate12 := by
  have hi : (cSpec12_1_11.first, cSpec12_1_11.firstUpper, trunkSpecIncoming cSpec12_1_11) = coordinateInput12_2 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_2
private theorem cEq12_1_11_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_11.second cSpec12_1_11.secondUpper (trunkSpecIncoming cSpec12_1_11)).map Prod.fst = coordinateCodes12_3.map decodeCoordinate12 := by
  have hi : (cSpec12_1_11.second, cSpec12_1_11.secondUpper, trunkSpecIncoming cSpec12_1_11) = coordinateInput12_3 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_3
private theorem cFlags12_1_11 : automaticFlags (trunkCatalog.states 12).context cSpec12_1_11 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_1_11_first, cEq12_1_11_second]
  decide +kernel
private abbrev cSpec12_1_12 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 1))[11]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_1_12_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_12.first cSpec12_1_12.firstUpper (trunkSpecIncoming cSpec12_1_12)).map Prod.fst = coordinateCodes12_0.map decodeCoordinate12 := by
  have hi : (cSpec12_1_12.first, cSpec12_1_12.firstUpper, trunkSpecIncoming cSpec12_1_12) = coordinateInput12_0 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_0
private theorem cEq12_1_12_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_12.second cSpec12_1_12.secondUpper (trunkSpecIncoming cSpec12_1_12)).map Prod.fst = coordinateCodes12_1.map decodeCoordinate12 := by
  have hi : (cSpec12_1_12.second, cSpec12_1_12.secondUpper, trunkSpecIncoming cSpec12_1_12) = coordinateInput12_1 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_1
private theorem cFlags12_1_12 : automaticFlags (trunkCatalog.states 12).context cSpec12_1_12 = [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  unfold automaticFlags
  rw [cEq12_1_12_first, cEq12_1_12_second]
  decide +kernel
private abbrev cSpec12_1_13 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 1))[12]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_1_13_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_13.first cSpec12_1_13.firstUpper (trunkSpecIncoming cSpec12_1_13)).map Prod.fst = coordinateCodes12_2.map decodeCoordinate12 := by
  have hi : (cSpec12_1_13.first, cSpec12_1_13.firstUpper, trunkSpecIncoming cSpec12_1_13) = coordinateInput12_2 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_2
private theorem cEq12_1_13_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_13.second cSpec12_1_13.secondUpper (trunkSpecIncoming cSpec12_1_13)).map Prod.fst = coordinateCodes12_20.map decodeCoordinate12 := by
  have hi : (cSpec12_1_13.second, cSpec12_1_13.secondUpper, trunkSpecIncoming cSpec12_1_13) = coordinateInput12_20 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_20
private theorem cFlags12_1_13 : automaticFlags (trunkCatalog.states 12).context cSpec12_1_13 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  unfold automaticFlags
  rw [cEq12_1_13_first, cEq12_1_13_second]
  decide +kernel
private abbrev cSpec12_1_14 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 1))[13]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_1_14_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_14.first cSpec12_1_14.firstUpper (trunkSpecIncoming cSpec12_1_14)).map Prod.fst = coordinateCodes12_21.map decodeCoordinate12 := by
  have hi : (cSpec12_1_14.first, cSpec12_1_14.firstUpper, trunkSpecIncoming cSpec12_1_14) = coordinateInput12_21 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_21
private theorem cEq12_1_14_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_1_14.second cSpec12_1_14.secondUpper (trunkSpecIncoming cSpec12_1_14)).map Prod.fst = coordinateCodes12_3.map decodeCoordinate12 := by
  have hi : (cSpec12_1_14.second, cSpec12_1_14.secondUpper, trunkSpecIncoming cSpec12_1_14) = coordinateInput12_3 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_3
private theorem cFlags12_1_14 : automaticFlags (trunkCatalog.states 12).context cSpec12_1_14 = [true, false, true, false, true] := by
  unfold automaticFlags
  rw [cEq12_1_14_first, cEq12_1_14_second]
  decide +kernel
private abbrev cSpec12_2_1 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[0]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_1_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_1.first cSpec12_2_1.firstUpper (trunkSpecIncoming cSpec12_2_1)).map Prod.fst = coordinateCodes12_2.map decodeCoordinate12 := by
  have hi : (cSpec12_2_1.first, cSpec12_2_1.firstUpper, trunkSpecIncoming cSpec12_2_1) = coordinateInput12_2 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_2
private theorem cEq12_2_1_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_1.second cSpec12_2_1.secondUpper (trunkSpecIncoming cSpec12_2_1)).map Prod.fst = coordinateCodes12_1.map decodeCoordinate12 := by
  have hi : (cSpec12_2_1.second, cSpec12_2_1.secondUpper, trunkSpecIncoming cSpec12_2_1) = coordinateInput12_1 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_1
private theorem cFlags12_2_1 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_1 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_2_1_first, cEq12_2_1_second]
  decide +kernel
private abbrev cSpec12_2_2 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[1]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_2_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_2.first cSpec12_2_2.firstUpper (trunkSpecIncoming cSpec12_2_2)).map Prod.fst = coordinateCodes12_4.map decodeCoordinate12 := by
  have hi : (cSpec12_2_2.first, cSpec12_2_2.firstUpper, trunkSpecIncoming cSpec12_2_2) = coordinateInput12_4 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_4
private theorem cEq12_2_2_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_2.second cSpec12_2_2.secondUpper (trunkSpecIncoming cSpec12_2_2)).map Prod.fst = coordinateCodes12_5.map decodeCoordinate12 := by
  have hi : (cSpec12_2_2.second, cSpec12_2_2.secondUpper, trunkSpecIncoming cSpec12_2_2) = coordinateInput12_5 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_5
private theorem cFlags12_2_2 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_2 = [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  unfold automaticFlags
  rw [cEq12_2_2_first, cEq12_2_2_second]
  decide +kernel
private abbrev cSpec12_2_3 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[2]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_3_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_3.first cSpec12_2_3.firstUpper (trunkSpecIncoming cSpec12_2_3)).map Prod.fst = coordinateCodes12_6.map decodeCoordinate12 := by
  have hi : (cSpec12_2_3.first, cSpec12_2_3.firstUpper, trunkSpecIncoming cSpec12_2_3) = coordinateInput12_6 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_6
private theorem cEq12_2_3_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_3.second cSpec12_2_3.secondUpper (trunkSpecIncoming cSpec12_2_3)).map Prod.fst = coordinateCodes12_7.map decodeCoordinate12 := by
  have hi : (cSpec12_2_3.second, cSpec12_2_3.secondUpper, trunkSpecIncoming cSpec12_2_3) = coordinateInput12_7 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_7
private theorem cFlags12_2_3 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_3 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_2_3_first, cEq12_2_3_second]
  decide +kernel
private abbrev cSpec12_2_4 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[3]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_4_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_4.first cSpec12_2_4.firstUpper (trunkSpecIncoming cSpec12_2_4)).map Prod.fst = coordinateCodes12_8.map decodeCoordinate12 := by
  have hi : (cSpec12_2_4.first, cSpec12_2_4.firstUpper, trunkSpecIncoming cSpec12_2_4) = coordinateInput12_8 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_8
private theorem cEq12_2_4_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_4.second cSpec12_2_4.secondUpper (trunkSpecIncoming cSpec12_2_4)).map Prod.fst = coordinateCodes12_9.map decodeCoordinate12 := by
  have hi : (cSpec12_2_4.second, cSpec12_2_4.secondUpper, trunkSpecIncoming cSpec12_2_4) = coordinateInput12_9 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_9
private theorem cFlags12_2_4 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_4 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_2_4_first, cEq12_2_4_second]
  decide +kernel
private abbrev cSpec12_2_5 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[4]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_5_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_5.first cSpec12_2_5.firstUpper (trunkSpecIncoming cSpec12_2_5)).map Prod.fst = coordinateCodes12_10.map decodeCoordinate12 := by
  have hi : (cSpec12_2_5.first, cSpec12_2_5.firstUpper, trunkSpecIncoming cSpec12_2_5) = coordinateInput12_10 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_10
private theorem cEq12_2_5_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_5.second cSpec12_2_5.secondUpper (trunkSpecIncoming cSpec12_2_5)).map Prod.fst = coordinateCodes12_11.map decodeCoordinate12 := by
  have hi : (cSpec12_2_5.second, cSpec12_2_5.secondUpper, trunkSpecIncoming cSpec12_2_5) = coordinateInput12_11 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_11
private theorem cFlags12_2_5 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_5 = [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  unfold automaticFlags
  rw [cEq12_2_5_first, cEq12_2_5_second]
  decide +kernel
private abbrev cSpec12_2_6 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[5]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_6_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_6.first cSpec12_2_6.firstUpper (trunkSpecIncoming cSpec12_2_6)).map Prod.fst = coordinateCodes12_22.map decodeCoordinate12 := by
  have hi : (cSpec12_2_6.first, cSpec12_2_6.firstUpper, trunkSpecIncoming cSpec12_2_6) = coordinateInput12_22 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_22
private theorem cEq12_2_6_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_6.second cSpec12_2_6.secondUpper (trunkSpecIncoming cSpec12_2_6)).map Prod.fst = coordinateCodes12_23.map decodeCoordinate12 := by
  have hi : (cSpec12_2_6.second, cSpec12_2_6.secondUpper, trunkSpecIncoming cSpec12_2_6) = coordinateInput12_23 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_23
private theorem cFlags12_2_6 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_6 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_2_6_first, cEq12_2_6_second]
  decide +kernel
private abbrev cSpec12_2_7 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[6]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_7_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_7.first cSpec12_2_7.firstUpper (trunkSpecIncoming cSpec12_2_7)).map Prod.fst = coordinateCodes12_24.map decodeCoordinate12 := by
  have hi : (cSpec12_2_7.first, cSpec12_2_7.firstUpper, trunkSpecIncoming cSpec12_2_7) = coordinateInput12_24 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_24
private theorem cEq12_2_7_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_7.second cSpec12_2_7.secondUpper (trunkSpecIncoming cSpec12_2_7)).map Prod.fst = coordinateCodes12_25.map decodeCoordinate12 := by
  have hi : (cSpec12_2_7.second, cSpec12_2_7.secondUpper, trunkSpecIncoming cSpec12_2_7) = coordinateInput12_25 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_25
private theorem cFlags12_2_7 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_7 = [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  unfold automaticFlags
  rw [cEq12_2_7_first, cEq12_2_7_second]
  decide +kernel
private abbrev cSpec12_2_8 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[7]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_8_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_8.first cSpec12_2_8.firstUpper (trunkSpecIncoming cSpec12_2_8)).map Prod.fst = coordinateCodes12_26.map decodeCoordinate12 := by
  have hi : (cSpec12_2_8.first, cSpec12_2_8.firstUpper, trunkSpecIncoming cSpec12_2_8) = coordinateInput12_26 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_26
private theorem cEq12_2_8_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_8.second cSpec12_2_8.secondUpper (trunkSpecIncoming cSpec12_2_8)).map Prod.fst = coordinateCodes12_27.map decodeCoordinate12 := by
  have hi : (cSpec12_2_8.second, cSpec12_2_8.secondUpper, trunkSpecIncoming cSpec12_2_8) = coordinateInput12_27 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_27
private theorem cFlags12_2_8 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_8 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_2_8_first, cEq12_2_8_second]
  decide +kernel
private abbrev cSpec12_2_9 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[8]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_9_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_9.first cSpec12_2_9.firstUpper (trunkSpecIncoming cSpec12_2_9)).map Prod.fst = coordinateCodes12_28.map decodeCoordinate12 := by
  have hi : (cSpec12_2_9.first, cSpec12_2_9.firstUpper, trunkSpecIncoming cSpec12_2_9) = coordinateInput12_28 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_28
private theorem cEq12_2_9_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_9.second cSpec12_2_9.secondUpper (trunkSpecIncoming cSpec12_2_9)).map Prod.fst = coordinateCodes12_29.map decodeCoordinate12 := by
  have hi : (cSpec12_2_9.second, cSpec12_2_9.secondUpper, trunkSpecIncoming cSpec12_2_9) = coordinateInput12_29 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_29
private theorem cFlags12_2_9 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_9 = [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  unfold automaticFlags
  rw [cEq12_2_9_first, cEq12_2_9_second]
  decide +kernel
private abbrev cSpec12_2_10 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[9]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_10_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_10.first cSpec12_2_10.firstUpper (trunkSpecIncoming cSpec12_2_10)).map Prod.fst = coordinateCodes12_30.map decodeCoordinate12 := by
  have hi : (cSpec12_2_10.first, cSpec12_2_10.firstUpper, trunkSpecIncoming cSpec12_2_10) = coordinateInput12_30 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_30
private theorem cEq12_2_10_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_10.second cSpec12_2_10.secondUpper (trunkSpecIncoming cSpec12_2_10)).map Prod.fst = coordinateCodes12_31.map decodeCoordinate12 := by
  have hi : (cSpec12_2_10.second, cSpec12_2_10.secondUpper, trunkSpecIncoming cSpec12_2_10) = coordinateInput12_31 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_31
private theorem cFlags12_2_10 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_10 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_2_10_first, cEq12_2_10_second]
  decide +kernel
private abbrev cSpec12_2_11 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[10]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_11_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_11.first cSpec12_2_11.firstUpper (trunkSpecIncoming cSpec12_2_11)).map Prod.fst = coordinateCodes12_32.map decodeCoordinate12 := by
  have hi : (cSpec12_2_11.first, cSpec12_2_11.firstUpper, trunkSpecIncoming cSpec12_2_11) = coordinateInput12_32 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_32
private theorem cEq12_2_11_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_11.second cSpec12_2_11.secondUpper (trunkSpecIncoming cSpec12_2_11)).map Prod.fst = coordinateCodes12_33.map decodeCoordinate12 := by
  have hi : (cSpec12_2_11.second, cSpec12_2_11.secondUpper, trunkSpecIncoming cSpec12_2_11) = coordinateInput12_33 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_33
private theorem cFlags12_2_11 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_11 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_2_11_first, cEq12_2_11_second]
  decide +kernel
private abbrev cSpec12_2_12 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[11]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_12_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_12.first cSpec12_2_12.firstUpper (trunkSpecIncoming cSpec12_2_12)).map Prod.fst = coordinateCodes12_34.map decodeCoordinate12 := by
  have hi : (cSpec12_2_12.first, cSpec12_2_12.firstUpper, trunkSpecIncoming cSpec12_2_12) = coordinateInput12_34 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_34
private theorem cEq12_2_12_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_12.second cSpec12_2_12.secondUpper (trunkSpecIncoming cSpec12_2_12)).map Prod.fst = coordinateCodes12_35.map decodeCoordinate12 := by
  have hi : (cSpec12_2_12.second, cSpec12_2_12.secondUpper, trunkSpecIncoming cSpec12_2_12) = coordinateInput12_35 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_35
private theorem cFlags12_2_12 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_12 = [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  unfold automaticFlags
  rw [cEq12_2_12_first, cEq12_2_12_second]
  decide +kernel
private abbrev cSpec12_2_13 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[12]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_13_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_13.first cSpec12_2_13.firstUpper (trunkSpecIncoming cSpec12_2_13)).map Prod.fst = coordinateCodes12_36.map decodeCoordinate12 := by
  have hi : (cSpec12_2_13.first, cSpec12_2_13.firstUpper, trunkSpecIncoming cSpec12_2_13) = coordinateInput12_36 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_36
private theorem cEq12_2_13_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_13.second cSpec12_2_13.secondUpper (trunkSpecIncoming cSpec12_2_13)).map Prod.fst = coordinateCodes12_37.map decodeCoordinate12 := by
  have hi : (cSpec12_2_13.second, cSpec12_2_13.secondUpper, trunkSpecIncoming cSpec12_2_13) = coordinateInput12_37 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_37
private theorem cFlags12_2_13 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_13 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_2_13_first, cEq12_2_13_second]
  decide +kernel
private abbrev cSpec12_2_14 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[13]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_14_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_14.first cSpec12_2_14.firstUpper (trunkSpecIncoming cSpec12_2_14)).map Prod.fst = coordinateCodes12_38.map decodeCoordinate12 := by
  have hi : (cSpec12_2_14.first, cSpec12_2_14.firstUpper, trunkSpecIncoming cSpec12_2_14) = coordinateInput12_38 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_38
private theorem cEq12_2_14_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_14.second cSpec12_2_14.secondUpper (trunkSpecIncoming cSpec12_2_14)).map Prod.fst = coordinateCodes12_39.map decodeCoordinate12 := by
  have hi : (cSpec12_2_14.second, cSpec12_2_14.secondUpper, trunkSpecIncoming cSpec12_2_14) = coordinateInput12_39 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_39
private theorem cFlags12_2_14 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_14 = [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  unfold automaticFlags
  rw [cEq12_2_14_first, cEq12_2_14_second]
  decide +kernel
private abbrev cSpec12_2_15 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[14]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_15_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_15.first cSpec12_2_15.firstUpper (trunkSpecIncoming cSpec12_2_15)).map Prod.fst = coordinateCodes12_40.map decodeCoordinate12 := by
  have hi : (cSpec12_2_15.first, cSpec12_2_15.firstUpper, trunkSpecIncoming cSpec12_2_15) = coordinateInput12_40 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_40
private theorem cEq12_2_15_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_15.second cSpec12_2_15.secondUpper (trunkSpecIncoming cSpec12_2_15)).map Prod.fst = coordinateCodes12_41.map decodeCoordinate12 := by
  have hi : (cSpec12_2_15.second, cSpec12_2_15.secondUpper, trunkSpecIncoming cSpec12_2_15) = coordinateInput12_41 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_41
private theorem cFlags12_2_15 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_15 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_2_15_first, cEq12_2_15_second]
  decide +kernel
private abbrev cSpec12_2_16 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[15]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_16_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_16.first cSpec12_2_16.firstUpper (trunkSpecIncoming cSpec12_2_16)).map Prod.fst = coordinateCodes12_42.map decodeCoordinate12 := by
  have hi : (cSpec12_2_16.first, cSpec12_2_16.firstUpper, trunkSpecIncoming cSpec12_2_16) = coordinateInput12_42 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_42
private theorem cEq12_2_16_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_16.second cSpec12_2_16.secondUpper (trunkSpecIncoming cSpec12_2_16)).map Prod.fst = coordinateCodes12_43.map decodeCoordinate12 := by
  have hi : (cSpec12_2_16.second, cSpec12_2_16.secondUpper, trunkSpecIncoming cSpec12_2_16) = coordinateInput12_43 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_43
private theorem cFlags12_2_16 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_16 = [true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_2_16_first, cEq12_2_16_second]
  decide +kernel
private abbrev cSpec12_2_17 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[16]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_17_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_17.first cSpec12_2_17.firstUpper (trunkSpecIncoming cSpec12_2_17)).map Prod.fst = coordinateCodes12_44.map decodeCoordinate12 := by
  have hi : (cSpec12_2_17.first, cSpec12_2_17.firstUpper, trunkSpecIncoming cSpec12_2_17) = coordinateInput12_44 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_44
private theorem cEq12_2_17_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_17.second cSpec12_2_17.secondUpper (trunkSpecIncoming cSpec12_2_17)).map Prod.fst = coordinateCodes12_45.map decodeCoordinate12 := by
  have hi : (cSpec12_2_17.second, cSpec12_2_17.secondUpper, trunkSpecIncoming cSpec12_2_17) = coordinateInput12_45 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_45
private theorem cFlags12_2_17 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_17 = [false, false, false, false, false, false, false, false, false, false] := by
  unfold automaticFlags
  rw [cEq12_2_17_first, cEq12_2_17_second]
  decide +kernel
private abbrev cSpec12_2_18 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[17]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_18_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_18.first cSpec12_2_18.firstUpper (trunkSpecIncoming cSpec12_2_18)).map Prod.fst = coordinateCodes12_46.map decodeCoordinate12 := by
  have hi : (cSpec12_2_18.first, cSpec12_2_18.firstUpper, trunkSpecIncoming cSpec12_2_18) = coordinateInput12_46 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_46
private theorem cEq12_2_18_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_18.second cSpec12_2_18.secondUpper (trunkSpecIncoming cSpec12_2_18)).map Prod.fst = coordinateCodes12_47.map decodeCoordinate12 := by
  have hi : (cSpec12_2_18.second, cSpec12_2_18.secondUpper, trunkSpecIncoming cSpec12_2_18) = coordinateInput12_47 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_47
private theorem cFlags12_2_18 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_18 = [true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_2_18_first, cEq12_2_18_second]
  decide +kernel
private abbrev cSpec12_2_19 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[18]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_19_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_19.first cSpec12_2_19.firstUpper (trunkSpecIncoming cSpec12_2_19)).map Prod.fst = coordinateCodes12_48.map decodeCoordinate12 := by
  have hi : (cSpec12_2_19.first, cSpec12_2_19.firstUpper, trunkSpecIncoming cSpec12_2_19) = coordinateInput12_48 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_48
private theorem cEq12_2_19_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_19.second cSpec12_2_19.secondUpper (trunkSpecIncoming cSpec12_2_19)).map Prod.fst = coordinateCodes12_49.map decodeCoordinate12 := by
  have hi : (cSpec12_2_19.second, cSpec12_2_19.secondUpper, trunkSpecIncoming cSpec12_2_19) = coordinateInput12_49 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_49
private theorem cFlags12_2_19 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_19 = [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  unfold automaticFlags
  rw [cEq12_2_19_first, cEq12_2_19_second]
  decide +kernel
private abbrev cSpec12_2_20 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[19]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_20_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_20.first cSpec12_2_20.firstUpper (trunkSpecIncoming cSpec12_2_20)).map Prod.fst = coordinateCodes12_50.map decodeCoordinate12 := by
  have hi : (cSpec12_2_20.first, cSpec12_2_20.firstUpper, trunkSpecIncoming cSpec12_2_20) = coordinateInput12_50 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_50
private theorem cEq12_2_20_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_20.second cSpec12_2_20.secondUpper (trunkSpecIncoming cSpec12_2_20)).map Prod.fst = coordinateCodes12_51.map decodeCoordinate12 := by
  have hi : (cSpec12_2_20.second, cSpec12_2_20.secondUpper, trunkSpecIncoming cSpec12_2_20) = coordinateInput12_51 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_51
private theorem cFlags12_2_20 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_20 = [true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_2_20_first, cEq12_2_20_second]
  decide +kernel
private abbrev cSpec12_2_21 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[20]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_21_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_21.first cSpec12_2_21.firstUpper (trunkSpecIncoming cSpec12_2_21)).map Prod.fst = coordinateCodes12_2.map decodeCoordinate12 := by
  have hi : (cSpec12_2_21.first, cSpec12_2_21.firstUpper, trunkSpecIncoming cSpec12_2_21) = coordinateInput12_2 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_2
private theorem cEq12_2_21_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_21.second cSpec12_2_21.secondUpper (trunkSpecIncoming cSpec12_2_21)).map Prod.fst = coordinateCodes12_23.map decodeCoordinate12 := by
  have hi : (cSpec12_2_21.second, cSpec12_2_21.secondUpper, trunkSpecIncoming cSpec12_2_21) = coordinateInput12_23 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_23
private theorem cFlags12_2_21 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_21 = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_2_21_first, cEq12_2_21_second]
  decide +kernel
private abbrev cSpec12_2_22 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[21]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_22_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_22.first cSpec12_2_22.firstUpper (trunkSpecIncoming cSpec12_2_22)).map Prod.fst = coordinateCodes12_22.map decodeCoordinate12 := by
  have hi : (cSpec12_2_22.first, cSpec12_2_22.firstUpper, trunkSpecIncoming cSpec12_2_22) = coordinateInput12_22 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_22
private theorem cEq12_2_22_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_22.second cSpec12_2_22.secondUpper (trunkSpecIncoming cSpec12_2_22)).map Prod.fst = coordinateCodes12_1.map decodeCoordinate12 := by
  have hi : (cSpec12_2_22.second, cSpec12_2_22.secondUpper, trunkSpecIncoming cSpec12_2_22) = coordinateInput12_1 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_1
private theorem cFlags12_2_22 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_22 = [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  unfold automaticFlags
  rw [cEq12_2_22_first, cEq12_2_22_second]
  decide +kernel
private abbrev cSpec12_2_23 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[22]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_23_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_23.first cSpec12_2_23.firstUpper (trunkSpecIncoming cSpec12_2_23)).map Prod.fst = coordinateCodes12_32.map decodeCoordinate12 := by
  have hi : (cSpec12_2_23.first, cSpec12_2_23.firstUpper, trunkSpecIncoming cSpec12_2_23) = coordinateInput12_32 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_32
private theorem cEq12_2_23_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_23.second cSpec12_2_23.secondUpper (trunkSpecIncoming cSpec12_2_23)).map Prod.fst = coordinateCodes12_43.map decodeCoordinate12 := by
  have hi : (cSpec12_2_23.second, cSpec12_2_23.secondUpper, trunkSpecIncoming cSpec12_2_23) = coordinateInput12_43 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_43
private theorem cFlags12_2_23 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_23 = [true, true, true, true] := by
  unfold automaticFlags
  rw [cEq12_2_23_first, cEq12_2_23_second]
  decide +kernel
private abbrev cSpec12_2_24 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[23]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_24_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_24.first cSpec12_2_24.firstUpper (trunkSpecIncoming cSpec12_2_24)).map Prod.fst = coordinateCodes12_42.map decodeCoordinate12 := by
  have hi : (cSpec12_2_24.first, cSpec12_2_24.firstUpper, trunkSpecIncoming cSpec12_2_24) = coordinateInput12_42 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_42
private theorem cEq12_2_24_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_24.second cSpec12_2_24.secondUpper (trunkSpecIncoming cSpec12_2_24)).map Prod.fst = coordinateCodes12_33.map decodeCoordinate12 := by
  have hi : (cSpec12_2_24.second, cSpec12_2_24.secondUpper, trunkSpecIncoming cSpec12_2_24) = coordinateInput12_33 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_33
private theorem cFlags12_2_24 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_24 = [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  unfold automaticFlags
  rw [cEq12_2_24_first, cEq12_2_24_second]
  decide +kernel
private abbrev cSpec12_2_25 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[24]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_25_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_25.first cSpec12_2_25.firstUpper (trunkSpecIncoming cSpec12_2_25)).map Prod.fst = coordinateCodes12_2.map decodeCoordinate12 := by
  have hi : (cSpec12_2_25.first, cSpec12_2_25.firstUpper, trunkSpecIncoming cSpec12_2_25) = coordinateInput12_2 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_2
private theorem cEq12_2_25_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_25.second cSpec12_2_25.secondUpper (trunkSpecIncoming cSpec12_2_25)).map Prod.fst = coordinateCodes12_20.map decodeCoordinate12 := by
  have hi : (cSpec12_2_25.second, cSpec12_2_25.secondUpper, trunkSpecIncoming cSpec12_2_25) = coordinateInput12_20 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_20
private theorem cFlags12_2_25 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_25 = [true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true] := by
  unfold automaticFlags
  rw [cEq12_2_25_first, cEq12_2_25_second]
  decide +kernel
private abbrev cSpec12_2_26 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 12) 2))[25]?).getD ⟨([],[]),false,([],[]),false,false,[]⟩
private theorem cEq12_2_26_first :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_26.first cSpec12_2_26.firstUpper (trunkSpecIncoming cSpec12_2_26)).map Prod.fst = coordinateCodes12_21.map decodeCoordinate12 := by
  have hi : (cSpec12_2_26.first, cSpec12_2_26.firstUpper, trunkSpecIncoming cSpec12_2_26) = coordinateInput12_21 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_21
private theorem cEq12_2_26_second :
    (trunkEndpointCases (trunkCatalog.states 12).context cSpec12_2_26.second cSpec12_2_26.secondUpper (trunkSpecIncoming cSpec12_2_26)).map Prod.fst = coordinateCodes12_43.map decodeCoordinate12 := by
  have hi : (cSpec12_2_26.second, cSpec12_2_26.secondUpper, trunkSpecIncoming cSpec12_2_26) = coordinateInput12_43 := by decide +kernel
  exact (congrArg (fun t : LowerPair × Bool × Bool => (trunkEndpointCases (trunkCatalog.states 12).context t.1 t.2.1 t.2.2).map Prod.fst) hi).trans hCoordinate12_43
private theorem cFlags12_2_26 : automaticFlags (trunkCatalog.states 12).context cSpec12_2_26 = [true] := by
  unfold automaticFlags
  rw [cEq12_2_26_first, cEq12_2_26_second]
  decide +kernel
private theorem keys_eq : coverageKeys (trunkCatalog.states 12) = checkedKeys := by
  rfl
private theorem tasks_eq : coverageTasks (trunkCatalog.states 12) = checkedTasks := by
  rw [← coverageTasksProjection_eq]
  change [(0,[(1, (automaticFlags (trunkCatalog.states 12).context cSpec12_0_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 12).context cSpec12_0_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 12).context cSpec12_0_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 12).context cSpec12_0_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 12).context cSpec12_0_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 12).context cSpec12_0_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 12).context cSpec12_0_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 12).context cSpec12_0_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 12).context cSpec12_0_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 12).context cSpec12_0_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 12).context cSpec12_0_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 12).context cSpec12_0_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 12).context cSpec12_0_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 12).context cSpec12_0_14).zipIdx.map Prod.swap)]),(1,[(1, (automaticFlags (trunkCatalog.states 12).context cSpec12_1_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 12).context cSpec12_1_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 12).context cSpec12_1_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 12).context cSpec12_1_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 12).context cSpec12_1_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 12).context cSpec12_1_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 12).context cSpec12_1_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 12).context cSpec12_1_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 12).context cSpec12_1_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 12).context cSpec12_1_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 12).context cSpec12_1_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 12).context cSpec12_1_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 12).context cSpec12_1_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 12).context cSpec12_1_14).zipIdx.map Prod.swap)]),(2,[(1, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_1).zipIdx.map Prod.swap),(2, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_2).zipIdx.map Prod.swap),(3, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_3).zipIdx.map Prod.swap),(4, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_4).zipIdx.map Prod.swap),(5, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_5).zipIdx.map Prod.swap),(6, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_6).zipIdx.map Prod.swap),(7, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_7).zipIdx.map Prod.swap),(8, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_8).zipIdx.map Prod.swap),(9, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_9).zipIdx.map Prod.swap),(10, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_10).zipIdx.map Prod.swap),(11, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_11).zipIdx.map Prod.swap),(12, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_12).zipIdx.map Prod.swap),(13, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_13).zipIdx.map Prod.swap),(14, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_14).zipIdx.map Prod.swap),(15, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_15).zipIdx.map Prod.swap),(16, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_16).zipIdx.map Prod.swap),(17, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_17).zipIdx.map Prod.swap),(18, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_18).zipIdx.map Prod.swap),(19, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_19).zipIdx.map Prod.swap),(20, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_20).zipIdx.map Prod.swap),(21, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_21).zipIdx.map Prod.swap),(22, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_22).zipIdx.map Prod.swap),(23, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_23).zipIdx.map Prod.swap),(24, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_24).zipIdx.map Prod.swap),(25, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_25).zipIdx.map Prod.swap),(26, (automaticFlags (trunkCatalog.states 12).context cSpec12_2_26).zipIdx.map Prod.swap)])] = checkedTasks
  rw [cFlags12_0_1, cFlags12_0_2, cFlags12_0_3, cFlags12_0_4, cFlags12_0_5, cFlags12_0_6, cFlags12_0_7, cFlags12_0_8, cFlags12_0_9, cFlags12_0_10, cFlags12_0_11, cFlags12_0_12, cFlags12_0_13, cFlags12_0_14, cFlags12_1_1, cFlags12_1_2, cFlags12_1_3, cFlags12_1_4, cFlags12_1_5, cFlags12_1_6, cFlags12_1_7, cFlags12_1_8, cFlags12_1_9, cFlags12_1_10, cFlags12_1_11, cFlags12_1_12, cFlags12_1_13, cFlags12_1_14, cFlags12_2_1, cFlags12_2_2, cFlags12_2_3, cFlags12_2_4, cFlags12_2_5, cFlags12_2_6, cFlags12_2_7, cFlags12_2_8, cFlags12_2_9, cFlags12_2_10, cFlags12_2_11, cFlags12_2_12, cFlags12_2_13, cFlags12_2_14, cFlags12_2_15, cFlags12_2_16, cFlags12_2_17, cFlags12_2_18, cFlags12_2_19, cFlags12_2_20, cFlags12_2_21, cFlags12_2_22, cFlags12_2_23, cFlags12_2_24, cFlags12_2_25, cFlags12_2_26]
  rfl
private theorem parents_length : (trunkRawParents (trunkCatalog.states 12).context).length = 625 := by
  decide +kernel
private theorem table_checked : coverageTable checkedKeys checkedTasks 625 := by
  apply coverageRemainder_sound _ _ _ [[179, 304, 359], [359, 484, 489, 609], [484, 489, 499]]
  unfold coverageRemainder parentsFor
  decide +kernel

theorem solution : trunkCoverage trunkCatalog 12 := by
  apply coverageTable_sound 12
  · unfold certRectangleValid; decide +kernel
  · decide +kernel
  · rw [keys_eq, tasks_eq, parents_length]
    exact table_checked
#print axioms solution
