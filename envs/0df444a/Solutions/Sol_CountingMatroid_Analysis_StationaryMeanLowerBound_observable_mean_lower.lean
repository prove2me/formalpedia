-- Prove2me | solution 1 for CountingMatroid.Analysis.StationaryMeanLowerBound.observable_mean_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:22:30.062589+00:00
-- url     : https://prove2.me/submissions/4ba8a8d5-e165-497a-a1b7-7e129c64f9ce

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
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanLowerBound
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
import Mathlib.Data.Fintype.Card
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
import Theorems.Thm_CountingMatroid_Analysis_AnnealingPartitionDrift_partition_step_bounds
import Theorems.Thm_CountingMatroid_Analysis_DefectPartitionPositive_defect_partition_pos
import Theorems.Thm_CountingMatroid_Analysis_StationaryMeanLowerBound_normalizer_decomposition

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
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.StationaryMeanLowerBound

open CountingMatroid.Model CountingMatroid.Program CountingMatroid.Model.Operations
open CountingMatroid.Analysis.StationaryMeanIdentities
open CountingMatroid.Analysis.PhaseObservationExperiment



/-- INTERNAL: Bounding off-diagonal types by all ordered pairs also covers
n=1, where there are no defect types.
TEXLINE: main.tex:1256-1263 -/
theorem defect_index_card_le (n : ℕ) : Fintype.card (DefectIndex n) ≤ n ^ 2 := by
  have hi : Function.Injective (fun index : DefectIndex n =>
      (index.emptyPair, index.fullPair)) := by
    rintro ⟨i, k, h⟩ ⟨i', k', h'⟩ he
    simpa only [Prod.mk.injEq, DefectIndex.mk.injEq] using he
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using
    Fintype.card_le_of_injective _ hi





end CountingMatroid.Analysis.StationaryMeanLowerBound

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.StationaryMeanLowerBound
end CountingMatroid.Analysis.StationaryMeanLowerBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.StationaryMeanLowerBound

open CountingMatroid.Model CountingMatroid.Program CountingMatroid.Model.Operations
open CountingMatroid.Analysis.StationaryMeanIdentities
open CountingMatroid.Analysis.PhaseObservationExperiment

/-- PAPER: main.tex:1241-1255
Every type mean and the ratio-observable mean is at least 1/(20 n²)
under good multipliers. The proof is over the actual normalized program
weights and uses the concrete schedule's factor-two partition step. -/
theorem solution (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (j : ℕ) (current : AnnealingCursor n)
    (hgood : FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂
      (CountingMatroid.Interface.Pseudocode.setup n p) j current)
    (index : Observable n) :
    1 / (20 * (n : ℚ) ^ 2) ≤ observableMean r o₁ o₂
      (CountingMatroid.Interface.Pseudocode.setup n p) j current index := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let q := s.ρ ^ j
  let C := TransversalPartition.partitionSum r o₁ o₂ q
  let w := current.currentWeights
  let Z := normalizer r o₁ o₂ q w
  have hρ := (AnnealingPartitionDrift.schedule_power_lower n p hn).1
  have hq : 0 < q := pow_pos hρ j
  have hC : 0 < C :=
    (AnnealingPartitionDrift.partition_step_bounds n r o₁ o₂ p hn j).1
  have hD (a : DefectIndex n) : 0 < FirstPhaseFailure.defectPartition r o₁ o₂ q a :=
    DefectPartitionPositive.defect_partition_pos r o₁ o₂ q hq a
  have hw (a : DefectIndex n) : 0 < w a :=
    (div_pos (div_pos hC (hD a)) (by norm_num : (0 : ℚ) < 4)).trans_le (hgood.2 a).1
  obtain ⟨hZ, ht, hu, hd⟩ := stationary_mean_identities r o₁ o₂ q s.ρ w hq hw
  have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hn2 : (1 : ℚ) ≤ (n : ℚ) ^ 2 := by nlinarith
  have hupper (a : DefectIndex n) : w a * FirstPhaseFailure.defectPartition r o₁ o₂ q a ≤ 4 * C := by
    have h := mul_le_mul_of_nonneg_right (hgood.2 a).2 (hD a).le
    change w a * FirstPhaseFailure.defectPartition r o₁ o₂ q a ≤
      (4 * (C / FirstPhaseFailure.defectPartition r o₁ o₂ q a)) *
        FirstPhaseFailure.defectPartition r o₁ o₂ q a at h
    have heq : (4 * (C / FirstPhaseFailure.defectPartition r o₁ o₂ q a)) *
        FirstPhaseFailure.defectPartition r o₁ o₂ q a = 4 * C := by
      field_simp [(hD a).ne']
    rwa [heq] at h
  have hZupper : Z ≤ 5 * (n : ℚ) ^ 2 * C := by
    dsimp only [Z]
    rw [normalizer_decomposition r o₁ o₂ q w hq hw]
    have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hupper a)
    have hcard : (Fintype.card (DefectIndex n) : ℚ) ≤ (n : ℚ) ^ 2 := by
      exact_mod_cast defect_index_card_le n
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    nlinarith [mul_le_mul_of_nonneg_right hcard (by positivity : (0 : ℚ) ≤ 4 * C)]
  have hsmall : 1 / (20 * (n : ℚ) ^ 2) ≤ (C / 4) / Z := by
    apply (le_div_iff₀ hZ).mpr
    rw [div_mul_eq_mul_div, one_mul]
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 20 * (n : ℚ) ^ 2)).mpr
    nlinarith [hZupper]
  have htype : 1 / (20 * (n : ℚ) ^ 2) ≤ typeMean r o₁ o₂ q w .transversal := by
    rw [ht]
    exact hsmall.trans (div_le_div_of_nonneg_right (by linarith : C / 4 ≤ C) hZ.le)
  cases index with
  | inl b =>
    cases b with
    | false => exact htype
    | true =>
      change 1 / (20 * (n : ℚ) ^ 2) ≤ numeratorMean r o₁ o₂ q s.ρ w
      rw [hu]
      have hnext := (AnnealingPartitionDrift.partition_step_bounds n r o₁ o₂ p hn j).2.1
      have hpower : q * s.ρ = s.ρ ^ (j + 1) := (pow_succ s.ρ j).symm
      rw [hpower]
      exact hsmall.trans (div_le_div_of_nonneg_right (by linarith :
        C / 4 ≤ TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ (j + 1))) hZ.le)
  | inr pair =>
    rcases pair with ⟨i, k⟩
    by_cases hik : i = k
    · simpa only [observableMean, if_pos hik] using htype
    · simp only [observableMean, if_neg hik]
      change 1 / (20 * (n : ℚ) ^ 2) ≤ typeMean r o₁ o₂ q w (.defect i k)
      let a : DefectIndex n := ⟨i, k, hik⟩
      rw [hd a]
      have hlow := mul_le_mul_of_nonneg_right (hgood.2 a).1 (hD a).le
      have heq : (C / FirstPhaseFailure.defectPartition r o₁ o₂ q a / 4) *
          FirstPhaseFailure.defectPartition r o₁ o₂ q a = C / 4 := by
        field_simp [(hD a).ne']
      rw [heq] at hlow
      exact hsmall.trans (div_le_div_of_nonneg_right hlow hZ.le)
