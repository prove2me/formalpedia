-- Prove2me | solution 1 for CountingMatroid.Analysis.InitialMultipliersGood.defect_partition_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:57:22.480995+00:00
-- url     : https://prove2.me/submissions/9f3b35d5-63d2-4a70-ba2c-373f48507c71

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_TransversalPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalProjection
import Definitions.Def_CountingMatroid_Interface_Pseudocode
import Definitions.Def_CountingMatroid_Interface_Pseudocode_Extension1
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_Analysis_InitialMultipliersGood_classify_defect_iff

namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.InitialMultipliersGood

open CountingMatroid.Model CountingMatroid.Analysis
open CountingMatroid.Program CountingMatroid.Model.Operations






















/-- INTERNAL: Membership in the encoded defect state recovers every free
Boolean choice without referring to a rank or independence oracle. -/
private theorem defect_choice_membership {n : ℕ} (index : DefectIndex n)
    (A : Finset (Fin n)) (i : Fin n) :
    ((i, false) ∈ defectChoiceState index A ↔
      (i ∈ ordinaryPairs index ∧ i ∉ A) ∨ i = index.fullPair) ∧
    ((i, true) ∈ defectChoiceState index A ↔
      (i ∈ ordinaryPairs index ∧ i ∈ A) ∨ i = index.fullPair) := by
  classical
  simp [defectChoiceState, or_comm]

/-- INTERNAL: The classifier accepts the encoded defect state for each
Boolean assignment on its ordinary pairs. -/
private theorem defect_choice_classified {n : ℕ} (index : DefectIndex n)
    (A : Finset (Fin n)) :
    (classifyState (defectChoiceState index A)).val =
      .defect index.emptyPair index.fullPair := by
  apply (classify_defect_iff _ index).mpr
  constructor <;> intro i
  all_goals
    rw [(defect_choice_membership index A i).1,
      (defect_choice_membership index A i).2]
    simp only [ordinaryPairs, Finset.mem_erase, Finset.mem_univ, and_true]
    by_cases he : i = index.emptyPair <;> by_cases hf : i = index.fullPair <;>
      by_cases hA : i ∈ A <;> simp_all [index.distinct, index.distinct.symm]

/-- INTERNAL: Every accepted defect state is recovered from the subset of
ordinary pairs at which it occupies y. This is the surjectivity half of the
initialization counting argument. -/
private theorem defect_choice_complete {n : ℕ} (index : DefectIndex n)
    (state : PairedSet n)
    (hkind : (classifyState state).val = .defect index.emptyPair index.fullPair) :
    defectChoiceState index
      ((ordinaryPairs index).filter (fun i => (i, true) ∈ state)) = state := by
  classical
  obtain ⟨he, hf⟩ := (classify_defect_iff state index).mp hkind
  ext ⟨i, b⟩
  have hei := he i
  have hfi := hf i
  cases b
  all_goals
    first | rw [(defect_choice_membership index _ i).1]
          | rw [(defect_choice_membership index _ i).2]
    simp only [ordinaryPairs, Finset.mem_erase, Finset.mem_univ, and_true,
      Finset.mem_filter]
    by_cases hx : (i, false) ∈ state <;> by_cases hy : (i, true) ∈ state
    all_goals simp only [hx, hy] at hei hfi ⊢
    all_goals tauto


/-- INTERNAL: Subsets of the ordinary pairs are recovered injectively from
their encoded defect states. -/
private theorem defect_choice_injective {n : ℕ} (index : DefectIndex n)
    (A B : Finset (Fin n)) (hA : A ⊆ ordinaryPairs index)
    (hB : B ⊆ ordinaryPairs index)
    (heq : defectChoiceState index A = defectChoiceState index B) : A = B := by
  classical
  ext i
  by_cases hi : i ∈ ordinaryPairs index
  · have hfull : i ≠ index.fullPair := (Finset.mem_erase.mp hi).1
    have hmem : ((i, true) ∈ defectChoiceState index A) ↔
        ((i, true) ∈ defectChoiceState index B) := by rw [heq]
    rw [(defect_choice_membership index A i).2,
      (defect_choice_membership index B i).2] at hmem
    simpa [hi, hfull] using hmem
  · have hnA : i ∉ A := fun h => hi (hA h)
    have hnB : i ∉ B := fun h => hi (hB h)
    simp [hnA, hnB]





end CountingMatroid.Analysis.InitialMultipliersGood

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.InitialMultipliersGood
end CountingMatroid.Analysis.InitialMultipliersGood
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.InitialMultipliersGood

open CountingMatroid.Model CountingMatroid.Analysis
open CountingMatroid.Program CountingMatroid.Model.Operations

/-- PAPER: main.tex:1148-1151
At q=1 an ordered defect has one free Boolean choice at each of the n-2
ordinary pairs; its operational partition sum is therefore 2^(n-2). -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (index : DefectIndex n) :
    FirstPhaseFailure.defectPartition r o₁ o₂ 1 index = (2 : ℚ) ^ (n - 2) := by
  classical
  have hcard : (ordinaryPairs index).card = n - 2 := by
    unfold ordinaryPairs
    rw [Finset.card_erase_of_mem (by simp [index.distinct.symm]),
      Finset.card_erase_of_mem (Finset.mem_univ index.emptyPair), Finset.card_univ]
    simp only [Fintype.card_fin]
    omega
  have hsum : (∑ A ∈ (ordinaryPairs index).powerset, (1 : ℚ)) =
      ∑ state ∈ Finset.univ.filter (fun state : PairedSet n =>
        (classifyState state).val = .defect index.emptyPair index.fullPair), (1 : ℚ) := by
    refine Finset.sum_bij (fun A _ => defectChoiceState index A) ?_ ?_ ?_ ?_
    · intro A _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact defect_choice_classified index A
    · intro A hA B hB heq
      exact defect_choice_injective index A B
        (Finset.mem_powerset.mp hA) (Finset.mem_powerset.mp hB) heq
    · intro state hstate
      refine ⟨(ordinaryPairs index).filter (fun i => (i, true) ∈ state),
        Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
      exact defect_choice_complete index state (Finset.mem_filter.mp hstate).2
    · intro A _
      rfl
  unfold FirstPhaseFailure.defectPartition
  simp only [one_pow]
  rw [← Finset.sum_filter, ← hsum]
  simp [Finset.card_powerset, hcard]
