-- Prove2me | solution 1 for CountingMatroid.Analysis.CoveredChainStepSubkernel.chain_step_nonhold_consumes_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:59:23.909752+00:00
-- url     : https://prove2.me/submissions/f8b3436e-4763-4140-bb2d-d7b4ff2efc19

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
import Theorems.Thm_CountingMatroid_Analysis_BoundedUniformReplay_boundedUniform_interval_replay
import Theorems.Thm_CountingMatroid_Analysis_BoundedUniformSuccessWords_sample_words_success_iff

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

/-!
Successful capped integer draws are characterized by their first accepted
word. The characterization records both the returned integer and the consumed
cursor, with all earlier fixed-width words rejected. Binary-word enumeration
counts the corresponding finite fair-bit cylinders exactly. Interval replay
then transfers fresh-suffix continuation bounds at each successful endpoint.
-/

namespace CountingMatroid.Analysis.BoundedUniformSuccessWords

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.BoundedUniformAbortMass



















/-- INTERNAL: A successful nonsingleton bounded draw has exactly k rejected
words followed by its returned value, and stops at that word's boundary.
TEXLINE: main.tex:1392-1401 -/
theorem bounded_uniform_success_words (tape : ℕ → Bool)
    (trials v start value stop : ℕ) (hv : 2 ≤ v) :
    (boundedUniform tape trials v start).val = (some value, stop) ↔
      ∃ k < trials,
        stop = start + (k + 1) * ((v - 1).log2 + 1) ∧
        value < v ∧
        (readWord tape ((v - 1).log2 + 1) 0
          (start + k * ((v - 1).log2 + 1))).1 = value ∧
        ∀ j < k, v ≤ (readWord tape ((v - 1).log2 + 1) 0
          (start + j * ((v - 1).log2 + 1))).1 := by
  rw [boundedUniform_value tape trials v start hv]
  exact sample_words_success_iff tape v trials start value stop









end CountingMatroid.Analysis.BoundedUniformSuccessWords

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · binary-word injectivity and finite-cardinality enumeration give the exact first-accepted-word cylinder mass. The sampler normal form identifies its stopping word uniquely, yielding the joint value/cursor law; successful interval replay and stopped_fiber_bound transfer a fresh-suffix continuation estimate. All declarations are proved.
-/

end

section


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

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain



/-- INTERNAL: A successful nonsingleton integer draw consumes at least one
whole rejection word; this excludes success using defaulted bits in a suffix
shorter than that word.
TEXLINE: main.tex:1392-1401 -/
theorem bounded_uniform_success_consumes_word
    (tape : ℕ → Bool) (trials v start value stop : ℕ) (hv : 2 ≤ v)
    (h : (boundedUniform tape trials v start).val = (some value, stop)) :
    start + ((v - 1).log2 + 1) ≤ stop := by
  obtain ⟨k, _, hstop, _, _, _⟩ :=
    (BoundedUniformSuccessWords.bounded_uniform_success_words
      tape trials v start value stop hv).mp h
  rw [hstop]
  have hm : ((v - 1).log2 + 1) ≤ (k + 1) * ((v - 1).log2 + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  omega







end CountingMatroid.Analysis.CoveredChainStepSubkernel

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · summed covered successful draw endpoints before composition, proved the occupied/complement selector bijections, identified rational acceptance and rejection with the Metropolis outcome average, and closed the full one-step subkernel comparison. All new support declarations are proved.
* 2026-10-09 · partial · proved the successful sampler value/cursor cylinder law and fixed-endpoint continuation bound in BoundedUniformSuccessWords, used them in the holding-mass proof, and strengthened nonholding consumption to two index words. The remaining branch is split at its first fair bit; aggregating the three adaptive draws and identifying selector uniformity with the Metropolis kernel remain open. No new unproved declaration introduced.
* 2026-10-09 · partial · proved minimum successful integer-word consumption, propagated it through every nonholding chain leaf, and bounded holding-only covered mass by one-half. The target now closes when n ≥ 2 and t ≤ (n - 1).log2 + 1, or when n ≥ 2 and trials = 0. The remaining obligation is the successful value/cursor counting law, with its required formula recorded at the open branch; no new proof debt introduced.
* 2026-10-09 · decomposed · isolated the covered one-transition comparison; zero suffix mass follows by replay onto an all-holding tape. Positive-length comparison needs successful rejection-word counting, then the established proposal geometry.
-/

end
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

/-- INTERNAL: Every nonholding successful chain attempt on a nonsingleton
ground consumes both complete index words after its laziness bit.
TEXLINE: main.tex:746-751,1392-1401 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (trials : ℕ) (q : ℚ) (weights : Multipliers n)
    (state next : PairedSet n) (start stop : ℕ) (hn : 2 ≤ n)
    (hb : tape start = false)
    (h : (chainStep r o₁ o₂ tape trials q weights state start).val =
      some (next, stop)) : start + 1 + 2 * ((n - 1).log2 + 1) ≤ stop := by
  unfold chainStep at h
  simp +instances only [Arlib.Computation.Charged.val_bind,
    Model.Operations.fairBit, Model.Operations.successor,
    Arlib.Computation.Charged.val_op, hb, Bool.false_eq_true, ite_false] at h
  cases ha : (boundedUniform tape trials n (start + 1)).val with
  | mk choice stopA =>
    cases choice with
    | none =>
      simp +instances only [ha, Arlib.Computation.Charged.val_pure] at h
      cases h
    | some value =>
      simp +instances only [ha, Arlib.Computation.Charged.val_bind] at h
      have hA := bounded_uniform_success_consumes_word tape trials n
        (start + 1) value stopA hn ha
      cases hb : (boundedUniform tape trials n stopA).val with
      | mk choiceB stopB =>
        cases choiceB with
        | none =>
          simp +instances only [hb, Arlib.Computation.Charged.val_pure] at h
          cases h
        | some valueB =>
          simp +instances only [hb, Arlib.Computation.Charged.val_bind] at h
          have hB := bounded_uniform_success_consumes_word tape trials n
            stopA valueB stopB hn hb
          have hC (v : ℕ) := (BoundedUniformReplay.boundedUniform_interval_replay
            trials v stopB tape).1
          dsimp only at hC
          split at h
          · simp +instances only [Arlib.Computation.Charged.val_bind,
              Model.Operations.erasePaired, Model.Operations.insertPaired,
              Arlib.Computation.Charged.val_opMany] at h
            split at h
            · have he := congrArg (fun out => out.map Prod.snd) h
              simp only [Arlib.Computation.Charged.val_pure, Option.map_some, Option.some.injEq] at he
              omega
            · simp +instances only [Arlib.Computation.Charged.val_bind] at h
              split at h
              · rename_i old new ho hn
                simp +instances only [Arlib.Computation.Charged.val_bind] at h
                split at h
                · simp +instances only [Arlib.Computation.Charged.val_bind,
                    Model.Operations.ratDiv, Model.Operations.rationalDenominator,
                    Model.Operations.rationalNumerator,
                    Arlib.Computation.Charged.val_opMany] at h
                  have hc := hC (new / old).den
                  split at h
                  · cases h
                  · simp +instances only [Arlib.Computation.Charged.val_bind] at h
                    split at h
                    all_goals
                      have he := congrArg (fun out => out.map Prod.snd) h
                      simp only [Arlib.Computation.Charged.val_pure, Option.map_some, Option.some.injEq] at he
                      omega
                · have he := congrArg (fun out => out.map Prod.snd) h
                  simp only [Arlib.Computation.Charged.val_pure, Option.map_some, Option.some.injEq] at he
                  omega
              · cases h
          · cases h
