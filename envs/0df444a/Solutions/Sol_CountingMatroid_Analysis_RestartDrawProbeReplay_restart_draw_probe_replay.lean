-- Prove2me | solution 1 for CountingMatroid.Analysis.RestartDrawProbeReplay.restart_draw_probe_replay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:37:25.076401+00:00
-- url     : https://prove2.me/submissions/2b979e2f-4afa-4152-85cc-be3bffa56fa2

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
import Theorems.Thm_CountingMatroid_Analysis_RestartDrawProbeReplay_probeStep_foldl
import Theorems.Thm_CountingMatroid_Analysis_RestartDrawProbeReplay_probedTransition_step

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
The phase-zero restart is exactly a fresh uniform transversal, with no return
excursion or restart-cap failure. The lemmas below retain the actual bit cursor
and the finite-tape suffix, rather than supplying a new random source.
-/

namespace CountingMatroid.Analysis.InitialRestartLaw

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: Split a charged fold's value at a list boundary. -/
private theorem foldl_append_value {α β : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell β)
    (xs ys : List α) (initial : β) :
    (Arlib.Computation.Charged.foldl f (xs ++ ys) initial).val =
      (Arlib.Computation.Charged.foldl f ys
        (Arlib.Computation.Charged.foldl f xs initial).val).val := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.cons_append, Arlib.Computation.Charged.val_foldl_cons]
        using ih (f initial x).val

/-- INTERNAL: Evaluate the fresh-bit scan on an indexed list, including its
cursor movement and all elements inserted into the actual paired set.
TEXLINE: main.tex:1163-1176 -/
private theorem fresh_scan_value {n : ℕ} (tape : ℕ → Bool) (k : ℕ)
    (indices : Fin k → Fin n) (state : PairedSet n) (cursor : ℕ) :
    (Arlib.Computation.Charged.foldl (fun acc i => do
      let bit ← fairBit tape acc.2
      let state ← insertPaired acc.1 (i, bit)
      let next ← successor acc.2
      pure (state, next)) (List.ofFn indices) (state, cursor)).val =
      (state ∪ Finset.univ.image (fun i : Fin k => (indices i, tape (cursor + i))),
        cursor + k) := by
  induction k generalizing state cursor with
  | zero => simp
  | succ k ih =>
      rw [List.ofFn_succ', List.concat_eq_append]
      change (Arlib.Computation.Charged.foldl _
        (List.ofFn (fun i : Fin k => indices i.castSucc) ++ [indices (Fin.last k)])
          (state, cursor)).val = _
      rw [foldl_append_value, ih]
      simp only [Arlib.Computation.Charged.val_foldl_cons,
        Arlib.Computation.Charged.val_foldl_nil, Arlib.Computation.Charged.val_bind,
        fairBit, insertPaired, successor, Arlib.Computation.Charged.val_op,
        Arlib.Computation.Charged.val_opMany, Arlib.Computation.Charged.val_pure]
      congr 1
      · rw [Fin.univ_castSuccEmb, Finset.cons_eq_insert, Finset.image_insert,
          Finset.map_eq_image, Finset.image_image]
        simp only [Fin.coe_castSuccEmb, Fin.val_last]
        simp only [Finset.union_insert]
        rfl

/-- PAPER: main.tex:1163-1176
A fresh restart reads precisely the next n bits and selects one element from
each pair. This equality also identifies the law when those bits are fair. -/
theorem freshTransversal_value (n : ℕ) (tape : ℕ → Bool) (cursor : ℕ) :
    (freshTransversal n tape cursor).val =
      (Finset.univ.image (fun i : Fin n => (i, tape (cursor + i))), cursor + n) := by
  simpa only [freshTransversal, ← List.ofFn_id, Finset.empty_union, id_eq] using
    fresh_scan_value tape n id (∅ : PairedSet n) cursor




















end CountingMatroid.Analysis.InitialRestartLaw

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r19 · proved · evaluated the actual fresh-bit scan and phase-zero restart,
  split finite tapes into equally weighted prefixes and observation suffixes,
  and derived the exact initial certificate-failure mass identity. No chain
  concentration bound, extra hypothesis, or unproved declaration introduced.
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









/-- INTERNAL: One stage of the probe meets the replay contract; its parameter
and stored multipliers do not read the tape. -/
theorem probedStage_step {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (ordinal : ℕ) (draw : Fin 3)
    (index : ℕ) :
    ProbeStep RestartCursor.bitCursor ordinal
      (fun tape acc => (probedStage r o₁ o₂ tape s tables ordinal draw index acc).val) := by
  have h := probeStep_foldl RestartCursor.bitCursor ordinal
    (fun tape acc (_ : ℕ) => probedTransition r o₁ o₂ tape s
      (ratPower s.ρ (successor index).val).val
      (learnedWeightRead tables (successor index).val s.L).val ordinal draw acc)
    (fun _ => probedTransition_step r o₁ o₂ s _ _ ordinal draw) (List.range s.τ)
  simpa only [probedStage, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.repeatFor] using h



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

/-- INTERNAL: An ordinal probe depends only on the tape before its reported
absolute cursor, even though the observed restart continues afterwards.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (j cursor : ℕ)
    (k : Fin (3 * s.restartCap)) :
    ChainStepIntervalReplay.SuccessReplay
      (fun tape => restartDrawProbe r o₁ o₂ tape s tables j cursor k)
      Prod.fst cursor := by
  have hfold := probeStep_foldl RestartCursor.bitCursor (k.val / 3)
    (fun tape acc index => probedStage r o₁ o₂ tape s tables (k.val / 3)
      ⟨k.val % 3, Nat.mod_lt _ (by decide)⟩ index acc)
    (fun index => probedStage_step r o₁ o₂ s tables (k.val / 3)
      ⟨k.val % 3, Nat.mod_lt _ (by decide)⟩ index) (List.range j)
  have hval : ∀ tape, restartDrawProbe r o₁ o₂ tape s tables j cursor k =
      (Arlib.Computation.Charged.foldl
        (fun acc index => probedStage r o₁ o₂ tape s tables (k.val / 3)
          ⟨k.val % 3, Nat.mod_lt _ (by decide)⟩ index acc) (List.range j)
        ((some ⟨Finset.univ.image (fun i : Fin n => (i, tape (cursor + i))),
          cursor + n, 0⟩, 0), none)).val.2 := by
    intro tape
    simp only [restartDrawProbe, probedRestart, Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.repeatFor,
      InitialRestartLaw.freshTransversal_value]
  intro tape d hd
  beta_reduce at hd ⊢
  rw [hval] at hd
  have hc := hfold.capture _ 0 (cursor + n) le_rfl tape d hd
  refine ⟨(Nat.le_add_right cursor n).trans hc.1, fun other hagree => ?_⟩
  rw [hval]
  have himage : Finset.univ.image (fun i : Fin n => (i, other (cursor + i))) =
      Finset.univ.image (fun i : Fin n => (i, tape (cursor + i))) := by
    congr 1
    funext i
    rw [hagree (cursor + i) (Nat.le_add_right _ _) (by have := i.isLt; have := hc.1; omega)]
  rw [himage]
  exact hc.2 other (fun i hlo hhi => hagree i ((Nat.le_add_right cursor n).trans hlo) hhi)
