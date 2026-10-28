-- Prove2me | solution 1 for CountingMatroid.Analysis.ProgramExchangeAcceptanceSubkernel.proposal_attempt_covered_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:29:56.347744+00:00
-- url     : https://prove2.me/submissions/bcf11193-2541-42c5-b5ed-dcde536b810a

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
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FiniteStoppedFiberMass
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_IdealExchangeChain
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_ProgramExchangeAcceptanceSubkernel
import Definitions.Def_CountingMatroid_Analysis_RationalAcceptanceSubkernel
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_SelectedMetropolisKernel
import Definitions.Def_CountingMatroid_Analysis_SelectedPairedBijection
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
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.Interval.Finset.Fin
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
import Theorems.Thm_CountingMatroid_Analysis_ProgramExchangeAcceptanceSubkernel_classified_weight_positive
import Theorems.Thm_CountingMatroid_Analysis_RationalAcceptanceSubkernel_rational_accept_covered_mass

namespace CountingMatroid.Analysis.BoundedUniformSubkernel
end CountingMatroid.Analysis.BoundedUniformSubkernel
namespace CountingMatroid.Analysis.BoundedUniformSuccessWords
end CountingMatroid.Analysis.BoundedUniformSuccessWords
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace CountingMatroid.Analysis.ObservationRoundDrawSites
end CountingMatroid.Analysis.ObservationRoundDrawSites
namespace CountingMatroid.Analysis.ClassifiedStateSelection
end CountingMatroid.Analysis.ClassifiedStateSelection
namespace CountingMatroid.Analysis.ExchangeProposalGeometry
end CountingMatroid.Analysis.ExchangeProposalGeometry
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
set_option backward.isDefEq.respectTransparency false

/-! Covered successful bounded draws are subuniform, including the zero-bit
singleton draw. The estimate sums all stopping cursors before composing a
fresh-suffix continuation. -/
namespace CountingMatroid.Analysis.BoundedUniformSubkernel
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.BoundedUniformSuccessWords

/-- INTERNAL: Every event on a finite fair suffix has mass at most one. -/
theorem fair_mass_le_one (head : List Bool) (t : ℕ) (E : (ℕ → Bool) → Prop) :
    fairMass head t E ≤ 1 := by
  classical
  calc
    fairMass head t E ≤ ∑ _ : List.Vector Bool t, 1 / (2 : ℝ) ^ t := by
      apply Finset.sum_le_sum
      intro bits _
      split_ifs <;> first | exact le_rfl | positivity
    _ = 1 := by simp [card_vector]













end CountingMatroid.Analysis.BoundedUniformSubkernel

end
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Match the executable classifier, weight computation and rational
acceptance branch to a single ideal accept/reject outcome. -/
namespace CountingMatroid.Analysis.ProgramExchangeAcceptanceSubkernel
end CountingMatroid.Analysis.ProgramExchangeAcceptanceSubkernel
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ProgramExchangeAcceptanceSubkernel
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.BoundedUniformSubkernel
open CountingMatroid.Analysis.SelectedMetropolisKernel
open CountingMatroid.Analysis.RationalAcceptanceSubkernel
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.StationaryMeanIdentities

/-- INTERNAL: The final executable proposal continuation is dominated by
one ideal Metropolis accept/reject outcome, including classifier rejection.
TEXLINE: main.tex:746-751,1392-1421 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (trials : ℕ) (q : ℚ) (weights : Multipliers n)
    (hq : 0 < q) (hw : ∀ a, 0 < weights a)
    (state candidate next : PairedSet n) (hvalid : (classifyState state).val ≠ .invalid)
    (head : List Bool) (t : ℕ) :
    fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
      proposalAttempt r o₁ o₂ trials q weights state candidate tape head.length =
        some (next, stop)) ≤
    exchangeOutcome state candidate next (min 1
      ((operationalLaw r o₁ o₂ q weights hq hw) candidate /
        (operationalLaw r o₁ o₂ q weights hq hw) state)) := by
  classical
  by_cases hc : (classifyState candidate).val = .invalid
  · have hz : (operationalLaw r o₁ o₂ q weights hq hw) candidate = 0 := by
      simp [operationalLaw, stateWeight, hc, weightOfKind]
    simp only [hz, zero_div, min_eq_right (by norm_num : (0 : ℝ) ≤ 1),
      exchangeOutcome, zero_mul, sub_zero, one_mul, zero_add]
    by_cases heq : state = next
    · rw [if_pos heq]
      exact fair_mass_le_one _ _ _
    · simp [fairMass, proposalAttempt, hc, heq, Option.some.injEq, Prod.mk.injEq]
  · obtain ⟨old, hold, hpos⟩ := classified_weight_positive r o₁ o₂ q weights hq hw state hvalid
    obtain ⟨new, hnew, hnewpos⟩ := classified_weight_positive r o₁ o₂ q weights hq hw candidate hc
    have hs : stateWeight r o₁ o₂ q weights state = old := by
      simp only [stateWeight, hold, Option.getD_some]
    have ht : stateWeight r o₁ o₂ q weights candidate = new := by
      simp only [stateWeight, hnew, Option.getD_some]
    have hnormal : (normalizer r o₁ o₂ q weights : ℝ) ≠ 0 := by
      exact_mod_cast (stationary_mean_identities r o₁ o₂ q 1 weights hq hw).1.ne'
    have hratio : (operationalLaw r o₁ o₂ q weights hq hw) candidate /
        (operationalLaw r o₁ o₂ q weights hq hw) state = (new / old : ℚ) := by
      change (stateWeight r o₁ o₂ q weights candidate : ℝ) / _ /
        ((stateWeight r o₁ o₂ q weights state : ℝ) / _) = _
      rw [hs, ht, div_div_div_cancel_right₀ hnormal, Rat.cast_div]
    have hevent (tape : ℕ → Bool) :
        proposalAttempt r o₁ o₂ trials q weights state candidate tape head.length =
          rationalAccept tape trials (new / old) state candidate head.length := by
      simp only [proposalAttempt, hc, if_false, hold, hnew]
    simp only [hevent, hratio]
    exact rational_accept_covered_mass head trials t (new / old)
      (div_pos hnewpos hpos).le state candidate next
