-- Prove2me | solution 1 for CountingMatroid.Analysis.CoveredChainIndexedSubkernel.covered_chain_indexed_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:34:35.216063+00:00
-- url     : https://prove2.me/submissions/2cb93107-2057-493c-ac81-f8662ba19fbc

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
import Theorems.Thm_CountingMatroid_Analysis_CoveredChainIndexedSubkernel_chain_step_nonholding_success
import Theorems.Thm_CountingMatroid_Analysis_CoveredChainIndexedSubkernel_fair_mass_split_bit
import Theorems.Thm_CountingMatroid_Analysis_CoveredChainIndexedSubkernel_two_draw_proposal_mass

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

/-! Finite uniform tape disintegration at a successful fixed endpoint cursor. -/
namespace CountingMatroid.Analysis.FiniteStoppedFiberMass















/-- INTERNAL: Inclusion of finite-tape events increases their mass. -/
theorem fairMass_mono (head : List Bool) (t : ℕ) (E F : (ℕ → Bool) → Prop)
    (h : ∀ bits : List.Vector Bool t,
      E (finiteTape (head ++ bits.val)) → F (finiteTape (head ++ bits.val))) :
    fairMass head t E ≤ fairMass head t F := by
  classical
  apply Finset.sum_le_sum
  intro bits _
  by_cases he : E (finiteTape (head ++ bits.val))
  · simp only [he, h bits he, if_true, le_refl]
  · simp only [he, if_false]
    split_ifs <;> positivity





end CountingMatroid.Analysis.FiniteStoppedFiberMass

end

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

/-- INTERNAL: The full covered finite-bit chain mass is bounded by the
lazy uniform-index accept/reject kernel, including both short and long tapes.
TEXLINE: main.tex:746-751,1392-1421 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (trials : ℕ) (q : ℚ) (weights : Multipliers n)
    (hn : 0 < n) (hq : 0 < q) (hw : ∀ a, 0 < weights a)
    (state next : PairedSet n) (hcard : state.card = n)
    (hvalid : (classifyState state).val ≠ .invalid)
    (head : List Bool) (t : ℕ) (ht : 0 < t) :
    fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
      (chainStep r o₁ o₂ tape trials q weights state head.length).val = some (next, stop)) ≤
      (1 / 2 : ℝ) * (if state = next then 1 else 0) +
      (1 / (2 * (n : ℝ) ^ 2)) * ∑ i : Fin n, ∑ j : Fin n,
        exchangeOutcome state (indexedCandidate state hcard i j) next (min 1
          ((operationalLaw r o₁ o₂ q weights hq hw) (indexedCandidate state hcard i j) /
            (operationalLaw r o₁ o₂ q weights hq hw) state)) := by
  classical
  let E := fun tape => ∃ stop, stop ≤ head.length + t ∧
    (chainStep r o₁ o₂ tape trials q weights state head.length).val = some (next, stop)
  let outcome := fun i j : Fin n => exchangeOutcome state (indexedCandidate state hcard i j)
    next (min 1 ((operationalLaw r o₁ o₂ q weights hq hw) (indexedCandidate state hcard i j) /
      (operationalLaw r o₁ o₂ q weights hq hw) state))
  have hholding : fairMass (head ++ [true]) (t - 1) E ≤
      if state = next then (1 : ℝ) else 0 := by
    by_cases heq : state = next
    · rw [if_pos heq]
      exact fair_mass_le_one _ _ _
    · rw [if_neg heq]
      have hz : fairMass (head ++ [true]) (t - 1) E = 0 := by
        unfold fairMass
        apply Finset.sum_eq_zero
        intro bits _
        apply if_neg
        rintro ⟨stop, hstop, hrun⟩
        have hb : finiteTape ((head ++ [true]) ++ bits.val) head.length = true := by
          unfold finiteTape
          rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]
          simp
        simp only [chainStep, Arlib.Computation.Charged.val_bind,
          Model.Operations.fairBit, Model.Operations.successor,
          Arlib.Computation.Charged.val_op, hb, ite_true,
          Arlib.Computation.Charged.val_pure, Option.some.injEq, Prod.mk.injEq] at hrun
        exact heq hrun.1
      exact hz.le
  have hnonholding : fairMass (head ++ [false]) (t - 1) E ≤
      (1 / (n : ℝ)) * ∑ i : Fin n, (1 / (n : ℝ)) * ∑ j : Fin n, outcome i j := by
    have hlen : (head ++ [false]).length = head.length + 1 := by simp
    have hend : (head ++ [false]).length + (t - 1) = head.length + t := by
      rw [hlen]
      omega
    apply le_trans (fairMass_mono (head ++ [false]) (t - 1) E
      (fun tape => ∃ (i : Fin n) (stopA : ℕ),
        stopA ≤ (head ++ [false]).length + (t - 1) ∧
        (boundedUniform tape trials n (head ++ [false]).length).val = (some i.val, stopA) ∧
        ∃ (j : Fin n) (stopB : ℕ), stopB ≤ (head ++ [false]).length + (t - 1) ∧
        (boundedUniform tape trials n stopA).val = (some j.val, stopB) ∧
        ∃ stop, stop ≤ (head ++ [false]).length + (t - 1) ∧
        proposalAttempt r o₁ o₂ trials q weights state (indexedCandidate state hcard i j)
          tape stopB = some (next, stop)) (by
      intro bits hs
      obtain ⟨stop, hstop, hrun⟩ := hs
      have hb : finiteTape ((head ++ [false]) ++ bits.val) head.length = false := by
        unfold finiteTape
        rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]
        simp
      obtain ⟨i, j, stopA, stopB, ha, hb, hp, hmA, hmB, hmC⟩ :=
        chain_step_nonholding_success r o₁ o₂ trials q weights state next hcard
          (finiteTape ((head ++ [false]) ++ bits.val)) head.length stop hb hrun
      refine ⟨i, stopA, by omega, ?_, j, stopB, by omega, hb, stop, by omega, hp⟩
      simpa only [hlen] using ha))
    exact two_draw_proposal_mass r o₁ o₂ trials q weights hn hq hw state next hcard hvalid
      (head ++ [false]) (t - 1)
  calc
    _ = (1 / 2 : ℝ) * fairMass (head ++ [true]) (t - 1) E +
        (1 / 2 : ℝ) * fairMass (head ++ [false]) (t - 1) E := fair_mass_split_bit head t ht E
    _ ≤ (1 / 2 : ℝ) * (if state = next then 1 else 0) +
        (1 / 2 : ℝ) * ((1 / (n : ℝ)) * ∑ i : Fin n,
          (1 / (n : ℝ)) * ∑ j : Fin n, outcome i j) :=
      add_le_add (mul_le_mul_of_nonneg_left hholding (by norm_num))
        (mul_le_mul_of_nonneg_left hnonholding (by norm_num))
    _ = _ := by
      rw [← Finset.mul_sum]
      have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp [hnreal]
      <;> ring
