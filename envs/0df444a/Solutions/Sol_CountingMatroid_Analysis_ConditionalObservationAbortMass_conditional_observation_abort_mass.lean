-- Prove2me | solution 1 for CountingMatroid.Analysis.ConditionalObservationAbortMass.conditional_observation_abort_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:36:22.995397+00:00
-- url     : https://prove2.me/submissions/6b6b82e9-9af5-46e7-a07b-e184701d9b24

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_ConditionalObservationAbortMass
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FiniteSuffixDrawAbortMass
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_ObservationRoundDrawSiteCovered
import Definitions.Def_CountingMatroid_Analysis_ObservationRoundDrawSites
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleDrawTrialsBridge
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
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
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
import Theorems.Thm_CountingMatroid_Analysis_ConditionalObservationAbortMass_repeatFor_first_abort
import Theorems.Thm_CountingMatroid_Analysis_ConditionalObservationAbortMass_repeatFor_value_succ
import Theorems.Thm_CountingMatroid_Analysis_FiniteSuffixDrawAbortMass_adaptive_draw_abort_mass
import Theorems.Thm_CountingMatroid_Analysis_ObservationRoundDrawCover_observation_round_draw_cover

namespace CountingMatroid.Analysis.ObservationRoundDrawCover
end CountingMatroid.Analysis.ObservationRoundDrawCover
namespace CountingMatroid.Analysis.RestartPhaseIntervalReplay
end CountingMatroid.Analysis.RestartPhaseIntervalReplay
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace CountingMatroid.Analysis.TraceReturnIntervalReplay
end CountingMatroid.Analysis.TraceReturnIntervalReplay
namespace CountingMatroid.Analysis.ObservePhaseIntervalReplay
end CountingMatroid.Analysis.ObservePhaseIntervalReplay
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
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.StoppingDrawPrefixCover
end CountingMatroid.Analysis.StoppingDrawPrefixCover
namespace CountingMatroid.Analysis.PhaseBitCursorBound
end CountingMatroid.Analysis.PhaseBitCursorBound
namespace CountingMatroid.Analysis.PhaseHistoryMultiplierLength
end CountingMatroid.Analysis.PhaseHistoryMultiplierLength
namespace CountingMatroid.Analysis.ChainStepBitBound
end CountingMatroid.Analysis.ChainStepBitBound
namespace CountingMatroid.Analysis.SuccessfulPrefixAbortBound
end CountingMatroid.Analysis.SuccessfulPrefixAbortBound
namespace CountingMatroid.Analysis.ObservationRoundDrawSites
end CountingMatroid.Analysis.ObservationRoundDrawSites
namespace CountingMatroid.Analysis.ClassifiedStateSelection
end CountingMatroid.Analysis.ClassifiedStateSelection
namespace CountingMatroid.Analysis.SuccessfulPhaseReplay
end CountingMatroid.Analysis.SuccessfulPhaseReplay
namespace CountingMatroid.Analysis.SinglePhaseIntervalReplay
end CountingMatroid.Analysis.SinglePhaseIntervalReplay
namespace CountingMatroid.Analysis.ChainStepNoninvalid
end CountingMatroid.Analysis.ChainStepNoninvalid
namespace CountingMatroid.Analysis.RestartPhaseTransversal
end CountingMatroid.Analysis.RestartPhaseTransversal
namespace CountingMatroid.Analysis.ScheduleResourceEnvelope
end CountingMatroid.Analysis.ScheduleResourceEnvelope
namespace CountingMatroid.Analysis.ScheduleCostEnvelope
end CountingMatroid.Analysis.ScheduleCostEnvelope
namespace CountingMatroid.Analysis.ScheduleValueEnvelope
end CountingMatroid.Analysis.ScheduleValueEnvelope
section


set_option autoImplicit false

/-!
The deterministic observation-loop failure characterization and the finite
union-bound reduction are proved below. The quantitative theorem uses two
separate open child obligations: the covered finite-suffix rejection law and
the operational construction of three draw-site prefix families. The
generic transfer to adaptive denominators is proved in the sampling child.
The original theorem statement and its zero-padded tape are unchanged.
-/

namespace CountingMatroid.Analysis.ConditionalObservationAbortMass

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment







/-- INTERNAL: Truncating the actual observation loop changes only its loop
bound. Stating this for an arbitrary schedule avoids reducing the entire
charged setup computation when using a concrete setup schedule.
TEXLINE: main.tex:1177-1187 -/
theorem observePhase_prefix_value {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool) (s : AnnealingSchedule)
    (q : ℚ) (w : Multipliers n) (k : ℕ) (start : PairedSet n × ℕ) :
    (observePhase r o₁ o₂ tape {s with observations := k} q w start).val =
      (Arlib.Computation.Charged.repeatFor (observationStep r o₁ o₂ tape s q w) k
        (some ⟨start.1, start.2, (Model.Operations.allocateCounts n).val, 0⟩)).val := by
  rfl





/-- INTERNAL: A concrete observation abort has a first failing iteration,
reached by the actual correlated trajectory on the same tape.
TEXLINE: main.tex:1177-1187,1392-1421 -/
theorem observePhase_abort_iff {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool) (s : AnnealingSchedule)
    (q : ℚ) (w : Multipliers n) (start : PairedSet n × ℕ) :
    (observePhase r o₁ o₂ tape s q w start).val = none ↔
      ∃ k < s.observations, ∃ current : ObservationCursor n,
        (Arlib.Computation.Charged.repeatFor (observationStep r o₁ o₂ tape s q w) k
          (some ⟨start.1, start.2, (Model.Operations.allocateCounts n).val, 0⟩)).val =
            some current ∧
        (observationStep r o₁ o₂ tape s q w k (some current)).val = none := by
  change (Arlib.Computation.Charged.repeatFor (observationStep r o₁ o₂ tape s q w)
    s.observations
    (some ⟨start.1, start.2, (Model.Operations.allocateCounts n).val, 0⟩)).val = none ↔ _
  exact repeatFor_first_abort _ (fun _ => rfl) _ _



end CountingMatroid.Analysis.ConditionalObservationAbortMass

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r26 · decomposed · reduced each reached-round estimate to a covered finite-suffix rejection law and an operational three-draw prefix-cover construction; the adaptive prefix-cylinder transfer is proved.

* r25 · reduced · proved first reached observation-failure witnesses and exact recording/iteration abort characterizations; the original mass bound reduces by a finite union bound to one adaptive reached-round capped-draw estimate, still open inside the parent.

* r24 · attempted · unfolded the actual observation loop; the capped-draw law must exclude invalid states and account for adaptive finite-block coverage after the restart.
-/

end
set_option autoImplicit false

/-!
The deterministic observation-loop failure characterization and the finite
union-bound reduction are proved below. The quantitative theorem uses two
separate open child obligations: the covered finite-suffix rejection law and
the operational construction of three draw-site prefix families. The
generic transfer to adaptive denominators is proved in the sampling child.
The original theorem statement and its zero-padded tape are unchanged.
-/

namespace CountingMatroid.Analysis.ConditionalObservationAbortMass
end CountingMatroid.Analysis.ConditionalObservationAbortMass
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ConditionalObservationAbortMass

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment

/-- INTERNAL: Conditional finite-suffix mass of an actual observation abort
after a successful restart. Only capped draws may abort a valid trajectory;
at most three such draws occur per observation transition.
TEXLINE: main.tex:1177-1187,1392-1421 -/
theorem solution (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    (Set.ncard {suffix : List Bool | suffix.length = t ∧
      (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s a) ∧
      ∃ current : AnnealingCursor n,
        BoundedRunPhaseHistory.phaseHistory r o₁ o₂
          (fun i => ((pref ++ suffix)[i]?).getD false) s j = some current ∧
        ∃ start,
          (restartPhase r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
            s current.tables j current.bitCursor).val = some start ∧
          (observePhase r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
            s (s.ρ ^ j) current.currentWeights start).val = none} : ENNReal) *
      (1 / 2 : ENNReal) ^ t ≤
        ENNReal.ofReal ((3 * (s.observations : ℚ) *
          (1 / 2 : ℚ) ^ s.drawTrials : ℚ) : ℝ) := by
  classical
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
  let E : Fin s.observations → Set (List Bool) := fun k =>
    {suffix | suffix.length = t ∧
      (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s a) ∧
      ∃ current : AnnealingCursor n,
        BoundedRunPhaseHistory.phaseHistory r o₁ o₂
          (fun i => ((pref ++ suffix)[i]?).getD false) s j = some current ∧
        ∃ start,
          (restartPhase r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
            s current.tables j current.bitCursor).val = some start ∧
          ∃ reached : ObservationCursor n,
            (Arlib.Computation.Charged.repeatFor
              (observationStep r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
                s (s.ρ ^ j) current.currentWeights) k.val
              (some ⟨start.1, start.2, (Model.Operations.allocateCounts n).val, 0⟩)).val =
                some reached ∧
            (observationStep r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
              s (s.ρ ^ j) current.currentWeights k.val (some reached)).val = none}
  have hevent : {suffix : List Bool | suffix.length = t ∧
      (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s a) ∧
      ∃ current : AnnealingCursor n,
        BoundedRunPhaseHistory.phaseHistory r o₁ o₂
          (fun i => ((pref ++ suffix)[i]?).getD false) s j = some current ∧
        ∃ start,
          (restartPhase r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
            s current.tables j current.bitCursor).val = some start ∧
          (observePhase r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
            s (s.ρ ^ j) current.currentWeights start).val = none} = ⋃ k, E k := by
    ext suffix
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, E, observePhase_abort_iff]
    constructor
    · rintro ⟨hlen, hprev, current, hh, start, hs, k, hk, reached, hrch, hb⟩
      exact ⟨⟨k, hk⟩, hlen, hprev, current, hh, start, hs, reached, hrch, hb⟩
    · rintro ⟨k, hlen, hprev, current, hh, start, hs, reached, hrch, hb⟩
      exact ⟨hlen, hprev, current, hh, start, hs, k.val, k.isLt, reached, hrch, hb⟩
  have hround (k : Fin s.observations) :
      (Set.ncard (E k) : ENNReal) * (1 / 2 : ENNReal) ^ t ≤
        ENNReal.ofReal ((3 * (1 / 2 : ℚ) ^ s.drawTrials : ℚ) : ℝ) := by
    obtain ⟨covers, hcover⟩ := ObservationRoundDrawCover.observation_round_draw_cover
      n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ hpositive j hj pref hprefix k.val k.isLt
    let D : Fin 3 → Set (List Bool) := fun site =>
      {suffix | suffix.length = t ∧
        ∃ head ∈ (covers site).prefixes, head <+: suffix ∧
          (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
            s.drawTrials ((covers site).denominator head)
            (pref.length + head.length)).val.1 = none}
    have hsubset : E k ⊆ ⋃ site, D site := by
      rintro suffix ⟨hlen, hprev, current, hh, start, hs, reached, hrch, hfail⟩
      have hshort :
          (observePhase r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
            {s with observations := k.val} (s.ρ ^ j)
            current.currentWeights start).val = some reached := by
        rw [observePhase_prefix_value]
        exact hrch
      have hlong :
          (observePhase r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
            {s with observations := k.val + 1} (s.ρ ^ j)
            current.currentWeights start).val = none := by
        rw [observePhase_prefix_value, repeatFor_value_succ, hrch]
        exact hfail
      obtain ⟨site, head, hhead, hpref, hdraw⟩ := hcover suffix hlen
        ⟨hprev, current, hh, start, hs, reached, hshort, hlong⟩
      exact Set.mem_iUnion.mpr ⟨site, hlen, head, hhead, hpref, hdraw⟩
    have hfinite : (⋃ site, D site).Finite :=
      (List.finite_length_eq Bool t).subset (by
        intro suffix hsuffix
        obtain ⟨site, hsite⟩ := Set.mem_iUnion.mp hsuffix
        exact hsite.1)
    have hcount : Set.ncard (E k) ≤ ∑ site, Set.ncard (D site) :=
      (Set.ncard_le_ncard hsubset hfinite).trans (Set.ncard_iUnion_le_of_fintype D)
    calc
      _ ≤ ∑ site, (Set.ncard (D site) : ENNReal) * (1 / 2 : ENNReal) ^ t := by
        rw [← Finset.sum_mul, ← Nat.cast_sum]
        exact mul_le_mul_left (Nat.cast_le.mpr hcount) _
      _ ≤ ∑ _site : Fin 3,
          ENNReal.ofReal (((1 / 2 : ℚ) ^ s.drawTrials : ℚ) : ℝ) := by
        apply Finset.sum_le_sum
        intro site _
        exact FiniteSuffixDrawAbortMass.adaptive_draw_abort_mass pref s.drawTrials t
          (covers site)
      _ = ENNReal.ofReal ((3 * (1 / 2 : ℚ) ^ s.drawTrials : ℚ) : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        push_cast
        ring
  change (Set.ncard _ : ENNReal) * (1 / 2 : ENNReal) ^ t ≤ _
  rw [hevent]
  calc
    (Set.ncard (⋃ k, E k) : ENNReal) * (1 / 2 : ENNReal) ^ t ≤
        ∑ k, (Set.ncard (E k) : ENNReal) * (1 / 2 : ENNReal) ^ t := by
      rw [← Finset.sum_mul, ← Nat.cast_sum]
      exact mul_le_mul_left (Nat.cast_le.mpr (Set.ncard_iUnion_le_of_fintype E)) _
    _ ≤ ∑ _k : Fin s.observations,
        ENNReal.ofReal ((3 * (1 / 2 : ℚ) ^ s.drawTrials : ℚ) : ℝ) :=
      Finset.sum_le_sum (fun k _ => hround k)
    _ = ENNReal.ofReal ((3 * (s.observations : ℚ) *
        (1 / 2 : ℚ) ^ s.drawTrials : ℚ) : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      push_cast
      ring
