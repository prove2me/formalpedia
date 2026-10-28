-- Prove2me | solution 1 for CountingMatroid.Analysis.SelectedMetropolisKernel.selected_metropolis_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:38:36.458769+00:00
-- url     : https://prove2.me/submissions/8a73461b-be70-470a-bbee-3ff39b29ae7c

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
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_IdealExchangeChain
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
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
import Theorems.Thm_CountingMatroid_Analysis_ExchangeProposalGeometry_exchange_proposal_average
import Theorems.Thm_CountingMatroid_Analysis_SelectedMetropolisKernel_metropolis_outcome_average

namespace CountingMatroid.Analysis.ExchangeProposalGeometry
end CountingMatroid.Analysis.ExchangeProposalGeometry
namespace Arlib
end Arlib
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
namespace CountingMatroid.Analysis.ClassifiedStateSelection
end CountingMatroid.Analysis.ClassifiedStateSelection
section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! The charged selector enumerates the occupied and unoccupied labels
without repetition, in the program's fixed x/y order. -/
namespace CountingMatroid.Analysis.SelectedPairedBijection
open CountingMatroid.Model CountingMatroid.Program





























/-- INTERNAL: Uniform in-range selection indices bijectively enumerate the
occupied or unoccupied labels, including n=1.
TEXLINE: main.tex:746-751 -/
theorem select_paired_bijective {n : ℕ} (state : PairedSet n) (occupied : Bool)
    (hcard : state.card = n) : Function.Bijective (selectedLabel state occupied hcard) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro i j hij
    apply Fin.ext
    have hval := congrArg Subtype.val hij
    exact (selectedLabels_nodup state occupied).getElem_inj_iff.mp hval
  · simp only [Fintype.card_fin, Fintype.card_coe]
    cases occupied <;> simp [Finset.card_compl, hcard, PairedGround] <;> omega

/-- INTERNAL: Transport a finite uniform index sum to the requested label set. -/
theorem select_paired_sum {n : ℕ} (state : PairedSet n) (occupied : Bool)
    (hcard : state.card = n) (F : PairedGround n → ℝ) :
    (∑ k : Fin n, F (selectedLabel state occupied hcard k).val) =
      ∑ a ∈ (if occupied then state else stateᶜ), F a := by
  classical
  have h := Fintype.sum_bijective (selectedLabel state occupied hcard)
    (select_paired_bijective state occupied hcard)
    (fun k => F (selectedLabel state occupied hcard k).val) (fun a => F a.val)
    (fun _ => rfl)
  simpa only [Finset.sum_coe_sort] using h

end CountingMatroid.Analysis.SelectedPairedBijection

end

section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! The ideal Metropolis kernel in the program's selection-index coordinates.
Rejected proposals contribute to the diagonal, including proposals of weight zero. -/
namespace CountingMatroid.Analysis.SelectedMetropolisKernel
open CountingMatroid.Model
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.SelectedPairedBijection
open Arlib.MarkovChains



/-- INTERNAL: Proposing the current state always returns it, independently
of the acceptance factor. -/
theorem exchange_outcome_self {α : Type} [DecidableEq α]
    (state next : α) (accept : ℝ) :
    exchangeOutcome state state next accept = if state = next then 1 else 0 := by
  by_cases h : state = next <;> simp [exchangeOutcome, h]





end CountingMatroid.Analysis.SelectedMetropolisKernel

end
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! The ideal Metropolis kernel in the program's selection-index coordinates.
Rejected proposals contribute to the diagonal, including proposals of weight zero. -/
namespace CountingMatroid.Analysis.SelectedMetropolisKernel
end CountingMatroid.Analysis.SelectedMetropolisKernel
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SelectedMetropolisKernel
open CountingMatroid.Model
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.SelectedPairedBijection
open Arlib.MarkovChains

/-- INTERNAL: The ideal chain is one-half holding plus the indexed
occupied/unoccupied accept/reject average used by the executable step.
TEXLINE: main.tex:746-751 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (weights : Multipliers n)
    (hn : 0 < n) (hq : 0 < q) (hw : ∀ a, 0 < weights a)
    (state next : PairedSet n) (hcard : state.card = n) :
    idealChain r o₁ o₂ q weights hn hq hw state next =
      (1 / 2 : ℝ) * (if state = next then 1 else 0) +
      (1 / (2 * (n : ℝ) ^ 2)) * ∑ i : Fin n, ∑ j : Fin n,
        exchangeOutcome state
          (insert (selectedLabel state false hcard j).val
            (state.erase (selectedLabel state true hcard i).val)) next
          (min 1 ((operationalLaw r o₁ o₂ q weights hq hw)
            (insert (selectedLabel state false hcard j).val
              (state.erase (selectedLabel state true hcard i).val)) /
            (operationalLaw r o₁ o₂ q weights hq hw) state)) := by
  classical
  let π := operationalLaw r o₁ o₂ q weights hq hw
  let F := fun candidate => exchangeOutcome state candidate next
    (min 1 (π candidate / π state))
  change metropolis π (exchangeProposal n hn) state next = _
  rw [metropolis_outcome_average,
    ExchangeProposalGeometry.exchange_proposal_average n hn state hcard F]
  dsimp only [F]
  rw [exchange_outcome_self]
  congr 2
  have houter := select_paired_sum state true hcard
    (fun a => ∑ b ∈ stateᶜ, F (insert b (state.erase a)))
  simp only [if_true] at houter
  rw [← houter]
  apply Finset.sum_congr rfl
  intro i _
  have hinner := select_paired_sum state false hcard
    (fun b => F (insert b (state.erase (selectedLabel state true hcard i).val)))
  simpa only [Bool.false_eq_true, if_false] using hinner.symm
