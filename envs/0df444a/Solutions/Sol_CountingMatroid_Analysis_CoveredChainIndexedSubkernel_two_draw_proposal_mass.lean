-- Prove2me | solution 1 for CountingMatroid.Analysis.CoveredChainIndexedSubkernel.two_draw_proposal_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:32:26.336686+00:00
-- url     : https://prove2.me/submissions/c9cb01c5-0e8b-4927-bf70-e2cc52d83e92

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
import Definitions.Def_CountingMatroid_Analysis_CoveredChainIndexedSubkernel
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
import Theorems.Thm_CountingMatroid_Analysis_BoundedUniformSubkernel_bounded_uniform_stopped_continuation
import Theorems.Thm_CountingMatroid_Analysis_BoundedUniformSubkernel_fair_mass_exists_le_sum
import Theorems.Thm_CountingMatroid_Analysis_ProgramExchangeAcceptanceSubkernel_proposal_attempt_covered_mass

namespace CountingMatroid.Analysis.ObservationRoundDrawSites
end CountingMatroid.Analysis.ObservationRoundDrawSites
namespace CountingMatroid.Analysis.ClassifiedStateSelection
end CountingMatroid.Analysis.ClassifiedStateSelection
namespace Arlib
end Arlib
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
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
namespace CountingMatroid.Analysis.BoundedUniformSubkernel
end CountingMatroid.Analysis.BoundedUniformSubkernel
namespace CountingMatroid.Analysis.BoundedUniformSuccessWords
end CountingMatroid.Analysis.BoundedUniformSuccessWords
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













/-- INTERNAL: Compose an adaptive bounded integer draw with value-dependent
fresh continuations; aborts and uncovered endpoints contribute zero.
TEXLINE: main.tex:1392-1401,1415-1421 -/
theorem bounded_uniform_bind_mass (head : List Bool) (trials v t : ℕ)
    (hv : 0 < v) (E : Fin v → (ℕ → Bool) → ℕ → Prop) (B : Fin v → ℝ)
    (hB : ∀ a, 0 ≤ B a)
    (hcont : ∀ (a : Fin v) (stop : ℕ), head.length ≤ stop → stop ≤ head.length + t →
      ∀ pref : List.Vector Bool (stop - head.length),
      (boundedUniform (finiteTape (head ++ pref.val)) trials v head.length).val =
        (some a.val, stop) →
      fairMass (head ++ pref.val) (t - (stop - head.length))
        (fun tape => E a tape stop) ≤ B a) :
    fairMass head t (fun tape => ∃ (a : Fin v) (stop : ℕ),
      stop ≤ head.length + t ∧
      (boundedUniform tape trials v head.length).val = (some a.val, stop) ∧
      E a tape stop) ≤ (1 / (v : ℝ)) * ∑ a : Fin v, B a := by
  calc
    _ ≤ ∑ a : Fin v, fairMass head t (fun tape => ∃ stop,
        stop ≤ head.length + t ∧
        (boundedUniform tape trials v head.length).val = (some a.val, stop) ∧
        E a tape stop) := fair_mass_exists_le_sum head t _
    _ ≤ ∑ a : Fin v, (1 / (v : ℝ)) * B a := Finset.sum_le_sum (fun a _ =>
      bounded_uniform_stopped_continuation head trials v t a.val hv a.isLt
        (E a) (B a) (hB a) (hcont a))
    _ = _ := (Finset.mul_sum _ _ _).symm

end CountingMatroid.Analysis.BoundedUniformSubkernel

end

section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Compose the three adaptive draw subkernels and the initial fair holding
bit in the selection-index coordinates of the executable chain. -/
namespace CountingMatroid.Analysis.CoveredChainIndexedSubkernel
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.BoundedUniformSubkernel
open CountingMatroid.Analysis.SelectedPairedBijection
open CountingMatroid.Analysis.SelectedMetropolisKernel
open CountingMatroid.Analysis.RationalAcceptanceSubkernel
open CountingMatroid.Analysis.ProgramExchangeAcceptanceSubkernel
open CountingMatroid.Analysis.IdealExchangeChain







/-- INTERNAL: Each indexed Metropolis accept/reject outcome has nonnegative mass. -/
theorem indexed_outcome_nonneg {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (weights : Multipliers n) (hq : 0 < q) (hw : ∀ a, 0 < weights a)
    (state candidate next : PairedSet n) :
    0 ≤ exchangeOutcome state candidate next (min 1
      ((operationalLaw r o₁ o₂ q weights hq hw) candidate /
        (operationalLaw r o₁ o₂ q weights hq hw) state)) := by
  let π := operationalLaw r o₁ o₂ q weights hq hw
  have hp : 0 ≤ min 1 (π candidate / π state) :=
    le_min zero_le_one (div_nonneg (π.coe_nonneg candidate) (π.coe_nonneg state))
  have hple : min 1 (π candidate / π state) ≤ 1 := min_le_left _ _
  apply add_nonneg
  · exact mul_nonneg hp (by split_ifs <;> positivity)
  · exact mul_nonneg (sub_nonneg.mpr hple) (by split_ifs <;> positivity)







end CountingMatroid.Analysis.CoveredChainIndexedSubkernel

end
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Compose the three adaptive draw subkernels and the initial fair holding
bit in the selection-index coordinates of the executable chain. -/
namespace CountingMatroid.Analysis.CoveredChainIndexedSubkernel
end CountingMatroid.Analysis.CoveredChainIndexedSubkernel
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.CoveredChainIndexedSubkernel
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.BoundedUniformSubkernel
open CountingMatroid.Analysis.SelectedPairedBijection
open CountingMatroid.Analysis.SelectedMetropolisKernel
open CountingMatroid.Analysis.RationalAcceptanceSubkernel
open CountingMatroid.Analysis.ProgramExchangeAcceptanceSubkernel
open CountingMatroid.Analysis.IdealExchangeChain

/-- INTERNAL: Compose both adaptive index draws with their final proposal
continuation, summing the stopped endpoints of each before the next draw.
TEXLINE: main.tex:746-751,1392-1421 -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (trials : ℕ) (q : ℚ) (weights : Multipliers n)
    (hn : 0 < n) (hq : 0 < q) (hw : ∀ a, 0 < weights a)
    (state next : PairedSet n) (hcard : state.card = n)
    (hvalid : (classifyState state).val ≠ .invalid) (head : List Bool) (t : ℕ) :
    fairMass head t (fun tape => ∃ (i : Fin n) (stopA : ℕ),
      stopA ≤ head.length + t ∧
      (boundedUniform tape trials n head.length).val = (some i.val, stopA) ∧
      ∃ (j : Fin n) (stopB : ℕ), stopB ≤ head.length + t ∧
      (boundedUniform tape trials n stopA).val = (some j.val, stopB) ∧
      ∃ stop, stop ≤ head.length + t ∧
      proposalAttempt r o₁ o₂ trials q weights state (indexedCandidate state hcard i j)
        tape stopB = some (next, stop)) ≤
    (1 / (n : ℝ)) * ∑ i : Fin n, (1 / (n : ℝ)) * ∑ j : Fin n,
      exchangeOutcome state (indexedCandidate state hcard i j) next (min 1
        ((operationalLaw r o₁ o₂ q weights hq hw) (indexedCandidate state hcard i j) /
          (operationalLaw r o₁ o₂ q weights hq hw) state)) := by
  let outcome := fun i j : Fin n =>
    exchangeOutcome state (indexedCandidate state hcard i j) next (min 1
      ((operationalLaw r o₁ o₂ q weights hq hw) (indexedCandidate state hcard i j) /
        (operationalLaw r o₁ o₂ q weights hq hw) state))
  have hpos (i j : Fin n) : 0 ≤ outcome i j :=
    indexed_outcome_nonneg r o₁ o₂ q weights hq hw state _ next
  apply bounded_uniform_bind_mass head trials n t hn _
    (fun i => (1 / (n : ℝ)) * ∑ j : Fin n, outcome i j)
    (fun i => mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => hpos i j)))
  intro i stopA hloA hhiA prefA hdrawA
  let headA := head ++ prefA.val
  let tA := t - (stopA - head.length)
  have hlenA : headA.length = stopA := by
    simp only [headA, List.length_append, prefA.property]
    omega
  have hendA : stopA + tA = head.length + t := by dsimp [tA]; omega
  have hbound := bounded_uniform_bind_mass headA trials n tA hn
    (fun j tape stopB => ∃ stop, stop ≤ head.length + t ∧
      proposalAttempt r o₁ o₂ trials q weights state (indexedCandidate state hcard i j)
        tape stopB = some (next, stop)) (outcome i) (hpos i) (by
    intro j stopB hloB hhiB prefB hdrawB
    let headB := headA ++ prefB.val
    let tB := tA - (stopB - headA.length)
    have hlenB : headB.length = stopB := by
      simp only [headB, List.length_append, prefB.property]
      omega
    have hendB : stopB + tB = head.length + t := by
      dsimp [tB]
      omega
    have hp := proposal_attempt_covered_mass r o₁ o₂ trials q weights hq hw
      state (indexedCandidate state hcard i j) next hvalid headB tB
    simpa only [hlenB, hendB] using hp)
  simpa only [hlenA, hendA] using hbound
