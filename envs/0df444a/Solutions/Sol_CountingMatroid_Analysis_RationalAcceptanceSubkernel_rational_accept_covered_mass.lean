-- Prove2me | solution 1 for CountingMatroid.Analysis.RationalAcceptanceSubkernel.rational_accept_covered_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:27:47.794635+00:00
-- url     : https://prove2.me/submissions/c4971df5-7680-43e2-9148-f88bab02e210

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
import Theorems.Thm_CountingMatroid_Analysis_ObservationRoundDrawSites_boundedUniform_result_lt
import Theorems.Thm_CountingMatroid_Analysis_RationalAcceptanceSubkernel_rational_draw_average

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
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! The exact numerator/denominator acceptance test is a finite-bit
subkernel of one rational Metropolis accept/reject decision. -/
namespace CountingMatroid.Analysis.RationalAcceptanceSubkernel
end CountingMatroid.Analysis.RationalAcceptanceSubkernel
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RationalAcceptanceSubkernel
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.BoundedUniformSubkernel
open CountingMatroid.Analysis.SelectedMetropolisKernel

/-- INTERNAL: Covered executions of the capped rational acceptance branch
are dominated by its exact Metropolis accept/reject distribution.
TEXLINE: main.tex:746-751,1392-1421 -/
theorem solution {α : Type} [DecidableEq α]
    (head : List Bool) (trials t : ℕ) (ratio : ℚ) (hr : 0 ≤ ratio)
    (state candidate next : α) :
    fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
      rationalAccept tape trials ratio state candidate head.length = some (next, stop)) ≤
    exchangeOutcome state candidate next (min 1 (ratio : ℝ)) := by
  classical
  by_cases hlt : ratio < 1
  · have hmin : min 1 (ratio : ℝ) = (ratio : ℝ) := min_eq_right (by exact_mod_cast hlt.le)
    rw [hmin, ← rational_draw_average ratio hr hlt state candidate next]
    apply le_trans (fairMass_mono head t _
      (fun tape => ∃ (a : Fin ratio.den) (stop : ℕ), stop ≤ head.length + t ∧
        (boundedUniform tape trials ratio.den head.length).val = (some a.val, stop) ∧
        (if a.val < ratio.num.natAbs then candidate else state) = next) (by
      intro bits hs
      obtain ⟨stop, hstop, hrun⟩ := hs
      unfold rationalAccept at hrun
      rw [if_pos hlt] at hrun
      cases hd : (boundedUniform (finiteTape (head ++ bits.val))
          trials ratio.den head.length).val with
      | mk choice cursor =>
        cases choice with
        | none => simp [hd] at hrun
        | some value =>
          simp only [hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrun
          have hv := ObservationRoundDrawSites.boundedUniform_result_lt
            (finiteTape (head ++ bits.val)) trials ratio.den head.length value
            (by rw [hd])
          refine ⟨(⟨value, hv⟩ : Fin ratio.den), cursor, ?_, rfl, hrun.1⟩
          omega))
    apply bounded_uniform_bind_mass head trials ratio.den t ratio.den_pos
      (fun a _ _ => (if a.val < ratio.num.natAbs then candidate else state) = next)
      (fun a => if (if a.val < ratio.num.natAbs then candidate else state) = next
        then (1 : ℝ) else 0)
      (fun a => by split_ifs <;> positivity)
    intro a stop hlo hhi pref hdraw
    by_cases heq : (if a.val < ratio.num.natAbs then candidate else state) = next
    · rw [if_pos heq]
      exact fair_mass_le_one _ _ _
    · simp [fairMass, heq]
  · have hmin : min 1 (ratio : ℝ) = 1 := min_eq_left (by exact_mod_cast (not_lt.mp hlt))
    rw [hmin]
    simp only [exchangeOutcome, one_mul, sub_self, zero_mul, add_zero]
    have hevent (tape : ℕ → Bool) :
        (∃ stop, stop ≤ head.length + t ∧
          rationalAccept tape trials ratio state candidate head.length = some (next, stop)) ↔
        candidate = next := by
      simp [rationalAccept, hlt, Option.some.injEq, Prod.mk.injEq]
    simp only [fairMass, hevent]
    by_cases heq : candidate = next
    · simp [heq, card_vector]
    · simp [heq]
