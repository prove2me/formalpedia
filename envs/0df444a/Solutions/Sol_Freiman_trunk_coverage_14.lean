-- Prove2me | solution 1 for Freiman.trunk_coverage_14
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:08:17.956694+00:00
-- url     : https://prove2.me/submissions/96010488-5507-46cf-b99b-2ea82f8d1e11

import Definitions.Def_Freiman_trunkGeometry
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

private def checkedKeys : List CoverageKey := [(0,[0,20],0,[-1]),
(0,[1,21],0,[-1]),
(0,[2,3,54],0,[-1]),
(0,[4,9,14,19,24,29,34,39,44,49,50,51,52,53,55,56,57,58,60,61,62,63,65,66,67,68,70,71,72,73,75,76,77,78,80,81,82,83,85,86,87,88,90,91,92,93,95,96,97,98],0,[-1]),
(0,[5,6,7,8,15,16,17,18,25,26,27,28,35,36,37,38,40,41,42,43,59,69,79,89,94],0,[-1]),
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
(0,[74],12,[0,1,2,3,4,5,6,7,8,9]),
(0,[74,99],14,[1,3]),
(0,[84],0,[-1]),
(0,[99],2,[0,1,2,3]),
(0,[99],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[99],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(0,[99],12,[0,1,2,3,4,5,6,7,8,9]),
(1,[0,10,20,30,45],0,[-1]),
(1,[1,11,21,31,46],0,[-1]),
(1,[2,3,54],0,[-1]),
(1,[4,9,14,19,24,29,34,39,44,49,50,51,52,53,55,56,57,58,60,61,62,63,65,66,67,68,70,71,72,73,75,76,77,78,80,81,82,83,85,86,87,88,90,91,92,93,95,96,97,98],0,[-1]),
(1,[5,6,7,8,15,16,17,18,25,26,27,28,35,36,37,38,40,41,42,43,59,69,79,89,94],0,[-1]),
(1,[12,64],0,[-1]),
(1,[13,23,33,48],0,[-1]),
(1,[22,32,47],0,[-1]),
(1,[74],0,[-1]),
(1,[84],0,[-1]),
(1,[99],2,[0,1,2,3]),
(1,[99],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(1,[99],7,[0,1,2,3]),
(1,[99],10,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(1,[99],12,[0,1,2,3,4,5,6,7,8,9]),
(1,[99],14,[1,3]),
(2,[0,10,20,30,45],0,[-1]),
(2,[1,11,21,31,46],0,[-1]),
(2,[2,3,54],0,[-1]),
(2,[4,9,14,19,24,29,34,39,44,49,50,51,52,53,55,56,57,58,60,61,62,63,65,66,67,68,70,71,72,73,75,76,77,78,80,81,82,83,85,86,87,88,90,91,92,93,95,96,97,98],0,[-1]),
(2,[5,6,7,8,15,16,17,18,25,26,27,28,35,36,37,38,40,41,42,43,59,69,79,89,94],0,[-1]),
(2,[12,64],0,[-1]),
(2,[13,23,33,48],0,[-1]),
(2,[22,32,47],0,[-1]),
(2,[74],0,[-1]),
(2,[84],0,[-1]),
(2,[99],2,[0,1,2,3]),
(2,[99],5,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),
(2,[99],7,[0,1,2,3,4,5,6,7,8,9]),
(2,[99],9,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[99],12,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[99],14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[99],17,[0,1,2,3,4,5,6,7,8,9]),
(2,[99],19,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
(2,[99],22,[0,1,2,3,4]),
(2,[99],24,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15])]
private def checkedTasks : List CoverageTask := [(0,[(1,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true)]),(2,[(0,false),(1,false),(2,false),(3,false)]),(3,[(0,true),(1,true),(2,true),(3,true)]),(4,[(0,true),(1,true),(2,true),(3,true)]),(5,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false)]),(6,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true)]),(7,[(0,false),(1,false),(2,false),(3,false)]),(8,[(0,true),(1,true),(2,true),(3,true)]),(9,[(0,true),(1,true),(2,true),(3,true)]),(10,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false)]),(11,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true)]),(12,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false)]),(13,[(0,true),(1,true)]),(14,[(0,true),(1,false),(2,true),(3,false),(4,true)])]),
(1,[(1,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true)]),(2,[(0,false),(1,false),(2,false),(3,false)]),(3,[(0,true),(1,true),(2,true),(3,true)]),(4,[(0,true),(1,true),(2,true),(3,true)]),(5,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false)]),(6,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true)]),(7,[(0,false),(1,false),(2,false),(3,false)]),(8,[(0,true),(1,true),(2,true),(3,true)]),(9,[(0,true),(1,true),(2,true),(3,true)]),(10,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false)]),(11,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true)]),(12,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false)]),(13,[(0,true),(1,true)]),(14,[(0,true),(1,false),(2,true),(3,false),(4,true)])]),
(2,[(1,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true)]),(2,[(0,false),(1,false),(2,false),(3,false)]),(3,[(0,true),(1,true),(2,true),(3,true)]),(4,[(0,true),(1,true),(2,true),(3,true)]),(5,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false)]),(6,[(0,true),(1,true),(2,true),(3,true)]),(7,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false)]),(8,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true)]),(9,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false),(16,false),(17,false),(18,false),(19,false),(20,false),(21,false),(22,false),(23,false),(24,false)]),(10,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true),(16,true),(17,true),(18,true),(19,true),(20,true),(21,true),(22,true),(23,true),(24,true)]),(11,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true)]),(12,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false),(16,false),(17,false),(18,false),(19,false),(20,false),(21,false),(22,false),(23,false),(24,false)]),(13,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true),(16,true),(17,true),(18,true),(19,true),(20,true),(21,true),(22,true),(23,true),(24,true)]),(14,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false),(16,false),(17,false),(18,false),(19,false),(20,false),(21,false),(22,false),(23,false),(24,false)]),(15,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true),(13,true),(14,true),(15,true),(16,true),(17,true),(18,true),(19,true),(20,true),(21,true),(22,true),(23,true),(24,true)]),(16,[(0,true),(1,true),(2,true),(3,true)]),(17,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false)]),(18,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true)]),(19,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false),(16,false),(17,false),(18,false),(19,false),(20,false),(21,false),(22,false),(23,false),(24,false)]),(20,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true),(8,true),(9,true)]),(21,[(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(7,true)]),(22,[(0,false),(1,false),(2,false),(3,false),(4,false)]),(23,[(0,true),(1,true),(2,true),(3,true)]),(24,[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(7,false),(8,false),(9,false),(10,false),(11,false),(12,false),(13,false),(14,false),(15,false)]),(25,[(0,true),(1,true)]),(26,[(0,true)])])]
private theorem keys_eq : coverageKeys (trunkCatalog.states 14) = checkedKeys := by
  rfl
private theorem tasks_eq : coverageTasks (trunkCatalog.states 14) = checkedTasks := by
  rw [← coverageTasksProjection_eq]
  decide +kernel
private theorem parents_length : (trunkRawParents (trunkCatalog.states 14).context).length = 100 := by
  decide +kernel
private theorem table_checked : coverageTable checkedKeys checkedTasks 100 := by
  unfold coverageTable coverageKeyRecorded
  decide +kernel

theorem solution : trunkCoverage trunkCatalog 14 := by
  apply coverageTable_sound 14
  · unfold certRectangleValid; decide +kernel
  · decide +kernel
  · rw [keys_eq, tasks_eq, parents_length]
    exact table_checked
#print axioms solution
