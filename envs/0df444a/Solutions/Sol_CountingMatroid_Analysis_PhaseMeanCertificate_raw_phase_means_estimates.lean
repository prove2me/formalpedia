-- Prove2me | solution 1 for CountingMatroid.Analysis.PhaseMeanCertificate.raw_phase_means_estimates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:15:04.189392+00:00
-- url     : https://prove2.me/submissions/cd3ac20c-cdef-42e2-9170-60a6406e7ac1

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
import Theorems.Thm_CountingMatroid_Analysis_AnnealingPartitionDrift_partition_step_bounds
import Theorems.Thm_CountingMatroid_Analysis_DefectPartitionPositive_defect_partition_pos

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
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
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.AnnealingPartitionDrift

open CountingMatroid.Model









/-- INTERNAL: A quotient of two nonnegative partition sums changes by at
most a factor two when both sums do. The zero-denominator case is retained
and uses Lean's division convention, rather than an unproved class-nonemptiness
claim. TEXLINE: main.tex:1141-1145 -/
private theorem quotient_step_bounds (a b a' b' : ℚ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha' : a / 2 ≤ a') (ha'upper : a' ≤ a)
    (hb' : b / 2 ≤ b') (hb'upper : b' ≤ b) :
    (a / b) / 2 ≤ a' / b' ∧ a' / b' ≤ 2 * (a / b) := by
  by_cases hbzero : b = 0
  · have hb'zero : b' = 0 := by rw [hbzero] at hb' hb'upper; linarith
    simp [hbzero, hb'zero]
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hbzero)
    have hb'pos : 0 < b' := (half_pos hbpos).trans_le hb'
    have ha'nonneg : 0 ≤ a' := (div_nonneg ha (by norm_num)).trans ha'
    constructor
    · have hl := div_le_div₀ ha'nonneg ha' hb'pos hb'upper
      have heq : (a / 2) / b = (a / b) / 2 := by ring
      rwa [heq] at hl
    · have hu := div_le_div₀ ha ha'upper (half_pos hbpos) hb'
      have heq : a / (b / 2) = 2 * (a / b) := by field_simp
      rwa [heq] at hu

/-- PAPER: main.tex:1141-1145,1266-1270
The ideal multiplier changes by at most a factor two at the next parameter.
This is proved for the concrete operational partition sums, including n=1
with no defect indices. No concentration estimate is used. -/
theorem ideal_multiplier_drift (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (j : ℕ) (index : DefectIndex n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let ideal := fun a => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ a) /
      FirstPhaseFailure.defectPartition r o₁ o₂ (s.ρ ^ a) index
    ideal j / 2 ≤ ideal (j + 1) ∧ ideal (j + 1) ≤ 2 * ideal j := by
  obtain ⟨hC, hClower, hCupper, hD⟩ := partition_step_bounds n r o₁ o₂ p hn j
  obtain ⟨hDnonneg, hDlower, hDupper⟩ := hD index
  exact quotient_step_bounds _ _ _ _ hC.le hDnonneg
    hClower hCupper hDlower hDupper

end CountingMatroid.Analysis.AnnealingPartitionDrift

end
set_option autoImplicit false

/-!
The raw phase boundary requires relative empirical errors about the normalized
operational state weights. `StationaryMeanIdentities` supplies their exact
type and annealing-observable mean identities using the classifier's
transversal reindexing. Positivity of the true ratio and drift of the ideal
multipliers are deterministic consequences of the concrete schedule and
partition sums, proved in `AnnealingPartitionDrift`. They need not be included
in an event whose probability is estimated. No stochastic estimate is asserted
by this module.
-/

namespace CountingMatroid.Analysis.PhaseMeanCertificate
end CountingMatroid.Analysis.PhaseMeanCertificate
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.PhaseMeanCertificate

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RelativeObservationBounds
open CountingMatroid.Analysis.StationaryMeanIdentities

/-- INTERNAL: Relative empirical errors certify the raw phase estimates;
the normalized state-weight identities supply the true means, and the schedule
supplies positivity and ideal-multiplier drift.
This bridge discharges those deterministic obligations for the phase-failure
probability proof, without assuming mixing or concentration.
TEXLINE: main.tex:1141-1145,1257-1270 -/
theorem solution (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (tape : ℕ → Bool) (j : ℕ)
    (hmeans : RawPhaseMeans r o₁ o₂ tape
      (CountingMatroid.Interface.Pseudocode.setup n p) j) :
    EmpiricalPhaseCertificate.RawPhaseEstimates r o₁ o₂ tape
      (CountingMatroid.Interface.Pseudocode.setup n p) j := by
  obtain ⟨current, start, observed, hcurrent, hgood, hstart, hobs,
    hN, hz, hu, hd⟩ := hmeans
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let q := s.ρ ^ j
  let C := fun a => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ a)
  have hρ : 0 < s.ρ := (AnnealingPartitionDrift.schedule_power_lower n p hn).1
  have hC : ∀ a, 0 < C a := fun a =>
    (AnnealingPartitionDrift.partition_step_bounds n r o₁ o₂ p hn a).1
  have hD (index : DefectIndex n) :
      0 < FirstPhaseFailure.defectPartition r o₁ o₂ q index :=
    DefectPartitionPositive.defect_partition_pos r o₁ o₂ q (pow_pos hρ _) index
  have hw (index : DefectIndex n) : 0 < current.currentWeights index :=
    (div_pos (div_pos (hC j) (hD index)) (by norm_num : (0 : ℚ) < 4)).trans_le
      (hgood.2 index).1
  obtain ⟨hZ, hpZero, hU, hpDefect⟩ := stationary_mean_identities r o₁ o₂ q s.ρ
    current.currentWeights (pow_pos hρ _) hw
  let pZero := typeMean r o₁ o₂ q current.currentWeights .transversal
  let pDefect := fun index : DefectIndex n => typeMean r o₁ o₂ q
    current.currentWeights (.defect index.emptyPair index.fullPair)
  have hpZeroPos : 0 < pZero := by
    dsimp only [pZero]
    rw [hpZero]
    exact div_pos (hC j) hZ
  have hUratio : numeratorMean r o₁ o₂ q s.ρ current.currentWeights =
      pZero * (C (j + 1) / C j) := by
    rw [hU]
    dsimp only [pZero]
    rw [hpZero]
    have hnext : q * s.ρ = s.ρ ^ (j + 1) := (pow_succ s.ρ j).symm
    rw [hnext]
    change C (j + 1) / _ = (C j / _) * (C (j + 1) / C j)
    field_simp [(hC j).ne']
  refine ⟨current, start, observed, hcurrent, hgood, hstart, hobs,
    pZero, pDefect, hN, hpZeroPos, div_pos (hC _) (hC _), hz, ?_, ?_⟩
  · rwa [hUratio] at hu
  · intro index
    have hpi : 0 < pDefect index := by
      dsimp only [pDefect]
      rw [hpDefect index]
      exact div_pos (mul_pos (hw index) (hD index)) hZ
    refine ⟨hw index, hpi, ?_,
      AnnealingPartitionDrift.ideal_multiplier_drift n r o₁ o₂ p hn j index,
      hd index⟩
    dsimp only [pZero, pDefect]
    rw [hpZero, hpDefect index]
    change _ = TransversalPartition.partitionSum r o₁ o₂ q /
      FirstPhaseFailure.defectPartition r o₁ o₂ q index
    field_simp [hZ.ne', (hw index).ne', (hD index).ne']
