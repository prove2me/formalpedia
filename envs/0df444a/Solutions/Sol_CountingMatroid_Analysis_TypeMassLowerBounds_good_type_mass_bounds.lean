-- Prove2me | solution 1 for CountingMatroid.Analysis.TypeMassLowerBounds.good_type_mass_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:33:07.026835+00:00
-- url     : https://prove2.me/submissions/94987eed-ef36-498e-b305-56abd7cc162e

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
import Definitions.Def_CountingMatroid_Analysis_AnnealingPartitionDrift
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
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
import Mathlib.Algebra.Order.Ring.Pow
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
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_Analysis_DefectPartitionPositive_defect_partition_pos
import Theorems.Thm_CountingMatroid_Analysis_TypeMassLowerBounds_normalizer_class_sum

namespace CountingMatroid.Analysis.TypeMassLowerBounds
end CountingMatroid.Analysis.TypeMassLowerBounds
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
namespace CountingMatroid.Analysis.BoundedRunOracleCalls
end CountingMatroid.Analysis.BoundedRunOracleCalls
namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
set_option autoImplicit false

namespace CountingMatroid.Analysis.TypeMassLowerBounds
end CountingMatroid.Analysis.TypeMassLowerBounds
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.TypeMassLowerBounds

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.StationaryMeanIdentities

/-- PAPER: main.tex:736-744
Good multipliers give polynomial lower bounds for every operational type
mean, including the empty defect family when `n = 1`. -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hn : 0 < n) (hq : 0 < q)
    (hgood : ∀ index,
      (TransversalPartition.partitionSum r o₁ o₂ q /
        FirstPhaseFailure.defectPartition r o₁ o₂ q index) / 4 ≤ w index ∧
      w index ≤ 4 * (TransversalPartition.partitionSum r o₁ o₂ q /
        FirstPhaseFailure.defectPartition r o₁ o₂ q index)) :
    normalizer r o₁ o₂ q w ≤
      5 * (n : ℚ) ^ 2 * TransversalPartition.partitionSum r o₁ o₂ q ∧
    1 / (5 * (n : ℚ) ^ 2) ≤ typeMean r o₁ o₂ q w .transversal ∧
    ∀ index : DefectIndex n, 1 / (20 * (n : ℚ) ^ 2) ≤
      typeMean r o₁ o₂ q w (.defect index.emptyPair index.fullPair) := by
  classical
  let C := TransversalPartition.partitionSum r o₁ o₂ q
  let D := FirstPhaseFailure.defectPartition r o₁ o₂ q
  have hC : 0 < C := by
    apply Finset.sum_pos
    · intro A _
      exact pow_pos hq _
    · exact Finset.univ_nonempty
  have hD (index : DefectIndex n) : 0 < D index :=
    DefectPartitionPositive.defect_partition_pos r o₁ o₂ q hq index
  have hw (index : DefectIndex n) : 0 < w index :=
    (div_pos (div_pos hC (hD index)) (by norm_num : (0 : ℚ) < 4)).trans_le
      (hgood index).1
  have hclass (index : DefectIndex n) :
      C / 4 ≤ w index * D index ∧ w index * D index ≤ 4 * C := by
    have hlo := mul_le_mul_of_nonneg_right (hgood index).1 (hD index).le
    have hhi := mul_le_mul_of_nonneg_right (hgood index).2 (hD index).le
    dsimp only [C, D] at *
    constructor
    · convert hlo using 1 <;> first | rfl | field_simp [(hD index).ne']
    · convert hhi using 1 <;> first | rfl | field_simp [(hD index).ne']
  have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hn2 : (1 : ℚ) ≤ (n : ℚ) ^ 2 := by nlinarith
  have hbound : normalizer r o₁ o₂ q w ≤ 5 * (n : ℚ) ^ 2 * C := by
    rw [normalizer_class_sum r o₁ o₂ q w hq hw]
    calc
      C + (∑ i : Fin n, ∑ k : Fin n,
          if h : i ≠ k then w ⟨i, k, h⟩ * D ⟨i, k, h⟩ else 0) ≤
          C + ∑ _i : Fin n, ∑ _k : Fin n, 4 * C := by
        apply add_le_add le_rfl
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro k _
        split_ifs with h
        · exact (hclass ⟨i, k, h⟩).2
        · positivity
      _ = (1 + 4 * (n : ℚ) ^ 2) * C := by simp; ring
      _ ≤ 5 * (n : ℚ) ^ 2 * C := by nlinarith [hC.le]
  obtain ⟨hZ, hz, _, hd⟩ := stationary_mean_identities r o₁ o₂ q 1 w hq hw
  refine ⟨hbound, ?_, ?_⟩
  · rw [hz]
    apply (div_le_div_iff₀ (by positivity) hZ).mpr
    simpa only [one_mul, mul_comm] using hbound
  · intro index
    rw [hd index]
    apply (div_le_div_iff₀ (by positivity) hZ).mpr
    have hb := mul_le_mul_of_nonneg_right (hclass index).1
      (by positivity : (0 : ℚ) ≤ 20 * (n : ℚ) ^ 2)
    nlinarith
