-- Prove2me | solution 1 for CountingMatroid.Analysis.RestartDrawProbeReplay.probedTransition_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:34:30.222912+00:00
-- url     : https://prove2.me/submissions/8768f433-203e-438b-8349-e6f0a274b197

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
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_RestartAttemptAccounting
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbe
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbeReplay
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbeScanReplay
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
import Theorems.Thm_CountingMatroid_Analysis_RestartDrawProbeScanReplay_probedBody_scan_count_mono
import Theorems.Thm_CountingMatroid_Analysis_RestartDrawProbeScanReplay_probedBody_scan_past
import Theorems.Thm_CountingMatroid_Analysis_RestartDrawProbeScanReplay_probedBody_scan_quiet_replay
import Theorems.Thm_CountingMatroid_Analysis_RestartDrawProbeScanReplay_probedBody_scan_replay

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
namespace CountingMatroid.Analysis.SuccessfulPrefixAbortBound
end CountingMatroid.Analysis.SuccessfulPrefixAbortBound
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

/-!
A concrete ordinal pre-draw probe for the counted restart. The probe observes
an allowed chain attempt before its trials and retains its first descriptor,
including when the ensuing attempt aborts. Forgetting the descriptor preserves
both components of the counted restart, not just its public result.
No stopping law, finite-block bound, or abort attribution is asserted here.
-/
namespace CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Model CountingMatroid.Program CountingMatroid.Model.Operations
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.ObservationRoundDrawSites































/-- INTERNAL: Early stopping retains the old invariant; continuing requires
it only for actual body results. -/
private theorem while_invariant {α β : Type} (P : β → Prop)
    (f : β → α → Arlib.Computation.Charged Op Cell (Option β))
    (h : ∀ b a next, P b → (f b a).val = some next → P next)
    (xs : List α) (b : β) (hb : P b) :
    P (Arlib.Computation.Charged.foldlWhile f xs b).val := by
  induction xs generalizing b with
  | nil => exact hb
  | cons a xs ih =>
    cases hf : (f b a).val with
    | none =>
      simp only [Arlib.Computation.Charged.val] at hf ⊢
      simpa only [Arlib.Computation.Charged.foldlWhile, hf] using hb
    | some next =>
      have hn := ih next (h b a next hb hf)
      simp only [Arlib.Computation.Charged.val] at hf hn ⊢
      simpa only [Arlib.Computation.Charged.foldlWhile, hf] using hn

/-- INTERNAL: A return scan cannot overwrite a descriptor captured before
that scan, irrespective of later tape bits or of a subsequent abort.
TEXLINE: main.tex:1392-1421 -/
theorem probed_return_retains {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (start : RestartCursor n) (count : ℕ)
    (d : ℕ × ℕ) :
    (probedReturn r o₁ o₂ tape s q w ordinal draw start count (some d)).val.2 = some d := by
  simp only [probedReturn, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.repeatWhile]
  apply while_invariant (fun acc => acc.2 = some d) _ ?_
    (List.range s.restartCap) (((some start, false), count), some d) rfl
  intro acc _ next ha he
  simp only [probedBody, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure, Option.map_eq_some_iff] at he
  obtain ⟨result, _, he⟩ := he
  cases he
  simp only [ha, Option.some_or]





end CountingMatroid.Analysis.RestartDrawProbe

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · return scans retain already-captured descriptors independently of later tape; used this latch in denominator positivity.
* 2026-10-09 · proved · concrete sticky ordinal probes preserve the counted body,
  return, transition, stage, and complete restart, including the abort cost.
-/

end

section


set_option autoImplicit false

/-!
Pre-draw replay for the concrete ordinal probe, independent of schedule
arithmetic, finite-prefix packaging, or probability. The probe's descriptor
depends only on the tape between the restart cursor and the descriptor's own
cursor, even though the counted state continues reading afterwards. The proof
packages a per-step replay contract (`ProbeStep`) — sticky capture, inert
death, silence past the ordinal, capture replay, and quiet whole-value replay
— shows it for one trace transition from the scan lemmas, and closes it under
the transition and stage folds.
-/
namespace CountingMatroid.Analysis.RestartDrawProbeReplay
open CountingMatroid.Model CountingMatroid.Program CountingMatroid.Model.Operations
open CountingMatroid.Analysis.RestartDrawProbe





/-- INTERNAL: Unfold the probe's return to its capped scan. -/
theorem probedReturn_val {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (start : RestartCursor n) (count : ℕ)
    (observed : Option (ℕ × ℕ)) :
    (probedReturn r o₁ o₂ tape s q w ordinal draw start count observed).val =
      (fun scan : ((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ) =>
        (((if scan.1.1.2 then scan.1.1.1 else none), scan.1.2), scan.2))
      (Arlib.Computation.Charged.foldlWhile
          (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc)
          (List.range s.restartCap) (((some start, false), count), observed)).val := rfl







end CountingMatroid.Analysis.RestartDrawProbeReplay

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · replay contract `ProbeStep` closed under folds; lifted
  the scan-level replay of `RestartDrawProbeScanReplay` to the whole restart.
* 2026-10-09 · open · exposed fixed-probe stage fold; generic absorbing-Option
  replay cannot replay the continuing product to the earlier observed cursor.
-/

end
set_option autoImplicit false

/-!
Pre-draw replay for the concrete ordinal probe, independent of schedule
arithmetic, finite-prefix packaging, or probability. The probe's descriptor
depends only on the tape between the restart cursor and the descriptor's own
cursor, even though the counted state continues reading afterwards. The proof
packages a per-step replay contract (`ProbeStep`) — sticky capture, inert
death, silence past the ordinal, capture replay, and quiet whole-value replay
— shows it for one trace transition from the scan lemmas, and closes it under
the transition and stage folds.
-/
namespace CountingMatroid.Analysis.RestartDrawProbeReplay
end CountingMatroid.Analysis.RestartDrawProbeReplay
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartDrawProbeReplay
open CountingMatroid.Model CountingMatroid.Program CountingMatroid.Model.Operations
open CountingMatroid.Analysis.RestartDrawProbe

/-- INTERNAL: One trace transition of the probe meets the replay contract,
by the scan-level replay lemmas. -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n) (ordinal : ℕ) (draw : Fin 3) :
    ProbeStep RestartCursor.bitCursor ordinal
      (fun tape acc => (probedTransition r o₁ o₂ tape s q w ordinal draw acc).val) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro tape acc d h
    obtain ⟨⟨st, count⟩, obs⟩ := acc
    cases st with
    | none => exact h
    | some cur =>
      simp only at h
      subst h
      exact probed_return_retains r o₁ o₂ tape s q w ordinal draw cur count d
  · intro tape count
    rfl
  · intro tape acc h1 h2
    obtain ⟨⟨st, count⟩, obs⟩ := acc
    simp only at h1 h2
    subst h1
    cases st with
    | none => exact ⟨rfl, h2⟩
    | some cur =>
      change (probedReturn r o₁ o₂ tape s q w ordinal draw cur count none).val.2 = none ∧
        ordinal < (probedReturn r o₁ o₂ tape s q w ordinal draw cur count none).val.1.2
      rw [probedReturn_val]
      refine ⟨RestartDrawProbeScanReplay.probedBody_scan_past r o₁ o₂ tape s q w ordinal draw
        _ _ count h2, ?_⟩
      exact h2.trans_le (RestartDrawProbeScanReplay.probedBody_scan_count_mono r o₁ o₂ tape s
        q w ordinal draw _ (((some cur, false), count), none))
  · intro cur count floor hfl tape out h
    have hr := RestartDrawProbeScanReplay.probedBody_scan_replay r o₁ o₂ s q w ordinal draw
      (List.range s.restartCap) (some cur, false) count floor
      (fun c hc => by cases hc; exact hfl) tape out (by
        change (probedReturn r o₁ o₂ tape s q w ordinal draw cur count none).val.2 = some out
          at h
        rw [probedReturn_val] at h
        exact h)
    refine ⟨hr.1, fun other hagree => ?_⟩
    change (probedReturn r o₁ o₂ other s q w ordinal draw cur count none).val.2 = some out
    rw [probedReturn_val]
    exact hr.2 other hagree
  · intro cur count floor hfl tape c count' h hle
    change (probedReturn r o₁ o₂ tape s q w ordinal draw cur count none).val =
      ((some c, count'), none) at h
    rw [probedReturn_val] at h
    cases hscan : (Arlib.Computation.Charged.foldlWhile
        (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc)
        (List.range s.restartCap) (((some cur, false), count), none)).val with
    | mk scan1 obs =>
    obtain ⟨⟨st, done⟩, cnt⟩ := scan1
    rw [hscan] at h
    cases done with
    | false => simp at h
    | true =>
      simp only [if_true, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      have hq := RestartDrawProbeScanReplay.probedBody_scan_quiet_replay r o₁ o₂ s q w ordinal
        draw (List.range s.restartCap) cur false count floor hfl tape c
        (by rw [hscan]) (by rw [hscan]) (by rw [hscan]; exact hle)
      refine ⟨hq.1, fun other hagree => ?_⟩
      show (probedReturn r o₁ o₂ other s q w ordinal draw cur count none).val = _
      rw [probedReturn_val, hq.2 other hagree, hscan]
      rfl
