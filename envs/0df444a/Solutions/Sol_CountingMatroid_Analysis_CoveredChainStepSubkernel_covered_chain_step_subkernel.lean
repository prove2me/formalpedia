-- Prove2me | solution 1 for CountingMatroid.Analysis.CoveredChainStepSubkernel.covered_chain_step_subkernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:36:28.183978+00:00
-- url     : https://prove2.me/submissions/ac370113-7a4c-4afa-8b36-ea7269609424

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
import Definitions.Def_CountingMatroid_Analysis_CoveredChainStepSubkernel
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
import Theorems.Thm_CountingMatroid_Analysis_BoundedUniformAbortMass_boundedUniform_value
import Theorems.Thm_CountingMatroid_Analysis_ChainStepIntervalReplay_chainStep_success_interval
import Theorems.Thm_CountingMatroid_Analysis_CoveredChainIndexedSubkernel_covered_chain_indexed_mass
import Theorems.Thm_CountingMatroid_Analysis_CoveredChainStepSubkernel_chain_step_nonhold_consumes_word
import Theorems.Thm_CountingMatroid_Analysis_CoveredChainStepSubkernel_covered_chain_mass_forced_hold
import Theorems.Thm_CountingMatroid_Analysis_ExchangeProposalGeometry_ideal_chain_lazy
import Theorems.Thm_CountingMatroid_Analysis_SelectedMetropolisKernel_selected_metropolis_kernel

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
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
The one-transition finite-bit subkernel needed for recorded observation paths.
Only successful transitions whose consumed interval fits in the supplied suffix
are counted. This isolates rejection sampling and Metropolis acceptance from
the quantitative whole-run coverage and stopping-prefix composition arguments.
The comparison is proved for every suffix length. Exact successful draw
mass is aggregated over all stopping cursors before composing fresh suffixes.
The occupied/unoccupied selector is a bijection, and the rational acceptance
branch, including its rejection contribution to the diagonal, agrees with the
ideal Metropolis accept/reject kernel.
-/

namespace CountingMatroid.Analysis.CoveredChainStepSubkernel
end CountingMatroid.Analysis.CoveredChainStepSubkernel
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.CoveredChainStepSubkernel

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain

/-- INTERNAL: Covered successful one-step sublaw is dominated by the ideal
Metropolis transition. The starting state has the program's valid n-element
shape. The consumed-cursor restriction prevents defaulted bits from acting
as additional fair randomness; no global schedule or warm law is used here.
TEXLINE: main.tex:746-751,1392-1421 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (trials : ℕ) (q : ℚ)
    (weights : Multipliers n) (hn : 0 < n) (hq : 0 < q)
    (hw : ∀ a, 0 < weights a) (head : List Bool) (t : ℕ)
    (state next : PairedSet n) (hcard : state.card = n)
    (hvalid : (classifyState state).val ≠ .invalid) :
    coveredChainStepMass r o₁ o₂ trials q weights head t state next ≤
      idealChain r o₁ o₂ q weights hn hq hw state next := by
  classical
  by_cases ht : t = 0
  · subst t
    have hzero : coveredChainStepMass r o₁ o₂ trials q weights head 0 state next = 0 := by
      unfold coveredChainStepMass
      apply Finset.sum_eq_zero
      intro suffix _
      apply if_neg
      rintro ⟨stop, hstop, hrun⟩
      have hreplay := ChainStepIntervalReplay.chainStep_success_interval
        r o₁ o₂ trials q weights state head.length
        (fun i => ((head ++ suffix.val)[i]?).getD false) (next, stop) hrun
      have heq := hreplay.2 (fun _ => true) (by
        intro i hlo hhi
        dsimp only at hhi
        omega)
      simp only [chainStep, Arlib.Computation.Charged.val_bind,
        Model.Operations.fairBit, Model.Operations.successor,
        Arlib.Computation.Charged.val_op, ite_true,
        Arlib.Computation.Charged.val_pure, Option.some.injEq,
        Prod.mk.injEq] at heq
      omega
    rw [hzero]
    exact (idealChain r o₁ o₂ q weights hn hq hw).coe_nonneg state next
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    by_cases hsmall : 2 ≤ n ∧ (t ≤ 2 * ((n - 1).log2 + 1) ∨ trials = 0)
    · have hm := covered_chain_mass_forced_hold r o₁ o₂ trials q weights
        head t state next htpos (by
          intro suffix stop hstop hrun
          cases hb : ((head ++ suffix.val)[head.length]?).getD false with
          | true => rfl
          | false =>
            rcases hsmall.2 with hshort | hcap
            · have hc := chain_step_nonhold_consumes_word r o₁ o₂
                (fun i => ((head ++ suffix.val)[i]?).getD false)
                trials q weights state next head.length stop hsmall.1 hb hrun
              omega
            · subst trials
              have hd : (boundedUniform
                  (fun i => ((head ++ suffix.val)[i]?).getD false)
                  0 n (head.length + 1)).val = (none, head.length + 1) := by
                rw [BoundedUniformAbortMass.boundedUniform_value _ 0 n _ hsmall.1]
                rfl
              simp +instances only [chainStep, Arlib.Computation.Charged.val_bind,
                Model.Operations.fairBit, Model.Operations.successor,
                Arlib.Computation.Charged.val_op, hb, Bool.false_eq_true,
                ite_false, hd, Arlib.Computation.Charged.val_pure] at hrun
              cases hrun)
      apply hm.trans
      by_cases heq : state = next
      · subst next
        rw [if_pos rfl]
        exact ExchangeProposalGeometry.ideal_chain_lazy r o₁ o₂ q weights hn hq hw state hcard
      · rw [if_neg heq]
        exact (idealChain r o₁ o₂ q weights hn hq hw).coe_nonneg state next
    · rw [SelectedMetropolisKernel.selected_metropolis_kernel
        r o₁ o₂ q weights hn hq hw state next hcard]
      have hm := CoveredChainIndexedSubkernel.covered_chain_indexed_mass
        r o₁ o₂ trials q weights hn hq hw state next hcard hvalid head t htpos
      have hrepr : coveredChainStepMass r o₁ o₂ trials q weights head t state next =
          FiniteStoppedFiberMass.fairMass head t (fun tape =>
            ∃ stop, stop ≤ head.length + t ∧
              (chainStep r o₁ o₂ tape trials q weights state head.length).val =
                some (next, stop)) := by
        unfold coveredChainStepMass FiniteStoppedFiberMass.fairMass
          FiniteStoppedFiberMass.finiteTape
        apply Finset.sum_congr rfl
        intro suffix _
        split_ifs <;> rfl
      rw [hrepr]
      simpa only [CoveredChainIndexedSubkernel.indexedCandidate] using hm
