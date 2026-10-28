-- Prove2me | solution 1 for CountingMatroid.Analysis.TransversalEventMean.large_pair_event_mean_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:04:57.513285+00:00
-- url     : https://prove2.me/submissions/76cc6820-df01-4a9e-8fe0-a40bfebf8aac

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
import Definitions.Def_CountingMatroidSupport_MarkovChains_Chains_Metropolis
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
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
import Definitions.Def_CountingMatroid_Analysis_IdealExchangeChain
import Definitions.Def_CountingMatroid_Analysis_ObservableProjection
import Definitions.Def_CountingMatroid_Analysis_ObservableVarianceDecomposition
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
import Definitions.Def_CountingMatroid_Analysis_TransversalEventMean
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
import Mathlib.Algebra.QuadraticDiscriminant
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

namespace Arlib
end Arlib
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

/-!
The event selection and conditional-mean part of the paper's defect transfer
argument. The exchange transport estimate is separate: these results do not
assert an energy bound for transferring a defect mean to this event.
-/

namespace CountingMatroid.Analysis.TransversalEventMean

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open Arlib.Probability











/-- INTERNAL: Weighted Cauchy--Schwarz bounds a finite event's centered
mean without any full-support requirement on its individual states.
TEXLINE: main.tex:909-911 -/
theorem event_centered_sum_sq_le {n : ℕ} (π : FinDist (PairedSet n))
    (H : PairedSet n → ℝ) (A : Finset (PairedSet n)) (c : ℝ) :
    (∑ state ∈ A, π state * (H state - c)) ^ 2 ≤
      eventMass π A * (∑ state ∈ A, π state * (H state - c) ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (f := fun state => π state) (g := fun state => π state * (H state - c) ^ 2)
    A (fun state _ => π.coe_nonneg state)
    (fun state _ => mul_nonneg (π.coe_nonneg state) (sq_nonneg _))
  intro state _
  exact le_of_eq (by ring)



end CountingMatroid.Analysis.TransversalEventMean

end
set_option autoImplicit false

/-!
The event selection and conditional-mean part of the paper's defect transfer
argument. The exchange transport estimate is separate: these results do not
assert an energy bound for transferring a defect mean to this event.
-/

namespace CountingMatroid.Analysis.TransversalEventMean
end CountingMatroid.Analysis.TransversalEventMean
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.TransversalEventMean

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open Arlib.Probability

/-- PAPER: main.tex:909-911
The conditional mean of a two-pair transversal event of probability at least
one quarter differs from the full transversal mean by at most four times
the transversal variance in squared deviation. -/
theorem solution {n : ℕ} (π : FinDist (PairedSet n))
    (H : PairedSet n → ℝ) (i k : Fin n) (a b : Bool)
    (hp : 0 < classMass π .transversal)
    (hlarge : classMass π .transversal / 4 ≤ eventMass π (pairEvent i k a b)) :
    (eventMean π H (pairEvent i k a b) - classMean π H .transversal) ^ 2 ≤
      4 * transversalVariance π H := by
  classical
  let A := pairEvent i k a b
  let p := classMass π .transversal
  let m := classMean π H .transversal
  let s := eventMass π A
  let T := ∑ state : PairedSet n,
    if (classifyState state).val = .transversal then π state * (H state - m) ^ 2 else 0
  have hs : 0 < s := (div_pos hp (by norm_num)).trans_le hlarge
  have hsum : (∑ state ∈ A, π state * (H state - m)) =
      s * (eventMean π H A - m) := by
    simp only [eventMean, mul_sub, Finset.sum_sub_distrib]
    change (∑ state ∈ A, π state * H state) - (∑ state ∈ A, π state * m) = _
    rw [← Finset.sum_mul]
    change _ = s * ((∑ state ∈ A, π state * H state) / s) - s * m
    rw [mul_div_cancel₀ _ hs.ne']
    rfl
  have hmoment : (∑ state ∈ A, π state * (H state - m) ^ 2) ≤ T := by
    dsimp only [A, pairEvent, T]
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro state _
    by_cases hT : (classifyState state).val = .transversal
    · simp only [hT, true_and, if_true]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (π.coe_nonneg state) (sq_nonneg _)
    · simp only [hT, false_and, if_false, le_refl]
  have hcs := event_centered_sum_sq_le π H A m
  rw [hsum] at hcs
  have hbound : s * (eventMean π H A - m) ^ 2 ≤ T := by
    have hmul := mul_le_mul_of_nonneg_left hmoment hs.le
    nlinarith [hcs]
  have hl : p ≤ 4 * s := by dsimp only [p, s, A]; linarith [hlarge]
  have hscaled : p * (eventMean π H A - m) ^ 2 ≤ 4 * T := by
    have hmul := mul_le_mul_of_nonneg_right hl
      (sq_nonneg (eventMean π H A - m))
    linarith
  change (eventMean π H A - m) ^ 2 ≤ 4 * (T / p)
  rw [← mul_div_assoc]
  exact (le_div_iff₀ hp).mpr (by nlinarith [hscaled])
