-- Prove2me | solution 1 for CountingMatroid.Analysis.RestartDrawProbe.restartDrawProbe_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:42:22.829226+00:00
-- url     : https://prove2.me/submissions/96c0305a-0df5-4df4-84bc-5c077c9d6918

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
import Theorems.Thm_CountingMatroid_Analysis_ObservationRoundDrawSites_chainDrawSite_positive

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





























/-- INTERNAL: Transfer a state invariant along a fixed charged fold. -/
private theorem fold_invariant {α β : Type} (P : β → Prop)
    (f : β → α → Arlib.Computation.Charged Op Cell β)
    (h : ∀ b a, P b → P (f b a).val) (xs : List α) (b : β) (hb : P b) :
    P (Arlib.Computation.Charged.foldl f xs b).val := by
  induction xs generalizing b with
  | nil => exact hb
  | cons a xs ih =>
    rw [Arlib.Computation.Charged.val_foldl_cons]
    exact ih _ (h b a hb)

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
set_option autoImplicit false

/-!
A concrete ordinal pre-draw probe for the counted restart. The probe observes
an allowed chain attempt before its trials and retains its first descriptor,
including when the ensuing attempt aborts. Forgetting the descriptor preserves
both components of the counted restart, not just its public result.
No stopping law, finite-block bound, or abort attribution is asserted here.
-/
namespace CountingMatroid.Analysis.RestartDrawProbe
end CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Model CountingMatroid.Program CountingMatroid.Model.Operations
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.ObservationRoundDrawSites

/-- INTERNAL: Every concrete ordinal restart probe has a positive denominator.
This proof needs no hypothesis about multiplier accuracy or tape coverage.
TEXLINE: main.tex:1392-1421 -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor : ℕ) (k : Fin (3 * s.restartCap)) (d : ℕ × ℕ) (hn : 0 < n)
    (hs : restartDrawProbe r o₁ o₂ tape s tables j cursor k = some d) : 0 < d.2 := by
  have hsite (q : ℚ) (w : Multipliers n) (ordinal : ℕ) (draw : Fin 3)
      (acc : (Option (RestartCursor n) × Bool) × ℕ) :
      PositiveObservation (bodySite r o₁ o₂ tape s q w ordinal draw acc) := by
    intro out hout
    unfold bodySite at hout
    split at hout
    · cases hout
    · cases hc : acc.1.1 with
      | none => simp only [hc] at hout; cases hout
      | some current =>
        simp only [hc] at hout
        split at hout
        · exact chainDrawSite_positive r o₁ o₂ tape s q w current.state
            current.bitCursor draw out hn hout
        · cases hout
  have hbody (q : ℚ) (w : Multipliers n) (ordinal : ℕ) (draw : Fin 3)
      (acc : ((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ))
      (next : ((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ))
      (ha : PositiveObservation acc.2)
      (he : (probedBody r o₁ o₂ tape s q w ordinal draw acc).val = some next) :
      PositiveObservation next.2 := by
    have hp : PositiveObservation
        (acc.2.or (bodySite r o₁ o₂ tape s q w ordinal draw acc.1)) := by
      cases ho : acc.2 with
      | none => simpa only [ho, Option.or] using hsite q w ordinal draw acc.1
      | some old => simpa only [ho, Option.some_or] using ha
    simp only [probedBody, Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_pure, Option.map_eq_some_iff] at he
    obtain ⟨result, _, he⟩ := he
    cases he
    exact hp
  have hreturn (q : ℚ) (w : Multipliers n) (ordinal : ℕ) (draw : Fin 3)
      (start : RestartCursor n) (count : ℕ) (observed : Option (ℕ × ℕ))
      (ho : PositiveObservation observed) :
      PositiveObservation
        (probedReturn r o₁ o₂ tape s q w ordinal draw start count observed).val.2 := by
    cases he : observed with
    | none =>
      simp only [he] at ho
      simp only [probedReturn, Arlib.Computation.Charged.val_bind,
        Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.repeatWhile]
      exact while_invariant (fun acc => PositiveObservation acc.2) _
        (fun b _ next hb he => hbody q w ordinal draw b next hb he)
        (List.range s.restartCap) (((some start, false), count), none) ho
    | some d =>
      simp only [he] at ho
      rw [probed_return_retains]
      exact ho
  have htransition (q : ℚ) (w : Multipliers n) (ordinal : ℕ) (draw : Fin 3)
      (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ))
      (ho : PositiveObservation acc.2) :
      PositiveObservation (probedTransition r o₁ o₂ tape s q w ordinal draw acc).val.2 := by
    cases hc : acc.1.1 with
    | none => simpa only [probedTransition, hc, Arlib.Computation.Charged.val_pure] using ho
    | some current =>
      simpa only [probedTransition, hc] using
        hreturn q w ordinal draw current acc.1.2 acc.2 ho
  have hstage (ordinal : ℕ) (draw : Fin 3) (index : ℕ)
      (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ))
      (ho : PositiveObservation acc.2) :
      PositiveObservation (probedStage r o₁ o₂ tape s tables ordinal draw index acc).val.2 := by
    simp only [probedStage, Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.repeatFor]
    exact fold_invariant (fun acc => PositiveObservation acc.2) _
      (fun b _ hb => htransition _ _ ordinal draw b hb) _ acc ho
  have hrestart (ordinal : ℕ) (draw : Fin 3) :
      PositiveObservation (probedRestart r o₁ o₂ tape s tables j cursor ordinal draw).val.2 := by
    simp only [probedRestart, Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.repeatFor]
    apply fold_invariant (fun acc => PositiveObservation acc.2) _
      (fun b index hb => hstage ordinal draw index b hb)
    intro out he
    cases he
  exact hrestart _ _ d hs
