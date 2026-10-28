-- Prove2me | solution 1 for CountingMatroid.Analysis.RestartDrawProbeScanReplay.probedBody_scan_quiet_replay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:03:26.193981+00:00
-- url     : https://prove2.me/submissions/6d622d56-0c8c-4ec8-b026-06345f2200a4

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
import Theorems.Thm_CountingMatroid_Analysis_ChainStepIntervalReplay_chainStep_success_interval
import Theorems.Thm_CountingMatroid_Analysis_RestartDrawProbeScanReplay_probedBody_scan_count_mono

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
Interval replay for the concrete ordinal probe's own accumulation, confined
to one capped return scan and lifted through the transition, stage and
restart folds. A captured descriptor can only ever change at the globally
unique attempt whose running count matches the probed ordinal; before that
attempt the probe is silent, and after it the descriptor is sticky.
-/
namespace CountingMatroid.Analysis.RestartDrawProbeScanReplay
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Analysis.ChainStepIntervalReplay
open CountingMatroid.Analysis.ObservationRoundDrawSites
open CountingMatroid.Analysis.RestartAttemptAccounting





/-- INTERNAL: Unfold one step of the probe's own capped-cost `foldlWhile`. -/
private theorem probedBody_scan_cons {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (a : ℕ) (xs : List ℕ)
    (acc : ((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ)) :
    (Arlib.Computation.Charged.foldlWhile
        (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) (a :: xs) acc).val =
      match (probedBody r o₁ o₂ tape s q w ordinal draw acc).val with
      | none => acc
      | some next =>
          (Arlib.Computation.Charged.foldlWhile
            (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs next).val := by
  cases hf : (probedBody r o₁ o₂ tape s q w ordinal draw acc).val with
  | none =>
    simp only [Arlib.Computation.Charged.val] at hf ⊢
    simp only [Arlib.Computation.Charged.foldlWhile, hf]
  | some next =>
    simp only [Arlib.Computation.Charged.val] at hf ⊢
    simp only [Arlib.Computation.Charged.foldlWhile, hf]



/-- INTERNAL: A done accumulator is absorbing for the probe's body,
regardless of the underlying state, ordinal, draw, or prior observation. -/
private theorem probedBody_done {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (st : Option (RestartCursor n)) (count : ℕ) :
    (probedBody r o₁ o₂ tape s q w ordinal draw (((st, true), count), none)).val = none := by
  unfold probedBody RestartAttemptAccounting.countedBody RestartAttemptAccounting.traceBody
  simp

/-- INTERNAL: A dead accumulator is absorbing for the probe's body,
regardless of the done flag, ordinal, draw, or prior observation. -/
private theorem probedBody_dead {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (done : Bool) (count : ℕ) :
    (probedBody r o₁ o₂ tape s q w ordinal draw (((none, done), count), none)).val = none := by
  unfold probedBody RestartAttemptAccounting.countedBody RestartAttemptAccounting.traceBody
  cases done <;> simp

/-- INTERNAL: One guarded, allowed step of the probe's body, refused branch:
the shared restart cap has already been reached for this cursor. -/
private theorem probedBody_refused {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (current : RestartCursor n) (count : ℕ)
    (hcap : ¬ current.attempts < s.restartCap) :
    (probedBody r o₁ o₂ tape s q w ordinal draw (((some current, false), count), none)).val =
      some (((none, true), count), none) := by
  have hcap' : ¬ (current.attempts < s.restartCap ∧ count = ordinal) := fun h => hcap h.1
  unfold probedBody RestartAttemptAccounting.countedBody RestartAttemptAccounting.traceBody
    bodySite RestartAttemptAccounting.attemptIncrement Operations.lessThan
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
    Arlib.Computation.Charged.val_op, decide_eq_true_eq,
    Bool.false_eq_true, if_false, if_neg hcap, if_neg hcap',
    Option.map_some, Nat.add_zero, Option.none_or]



/-- INTERNAL: One guarded, allowed, ordinal-matched step of the probe's
body: the probe observes exactly the chain's pre-draw site. -/
private theorem probedBody_eq {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (draw : Fin 3) (current : RestartCursor n) (count : ℕ)
    (hallow : current.attempts < s.restartCap) :
    (probedBody r o₁ o₂ tape s q w count draw (((some current, false), count), none)).val =
      match (chainStep r o₁ o₂ tape s.drawTrials q w current.state current.bitCursor).val with
      | none => some (((none, true), count + 1),
          chainDrawSite r o₁ o₂ tape s q w current.state current.bitCursor draw)
      | some (state, bitCursor) =>
          some (((some ⟨state, bitCursor, current.attempts + 1⟩,
                decide ((classifyState state).val = StateKind.transversal)), count + 1),
            chainDrawSite r o₁ o₂ tape s q w current.state current.bitCursor draw) := by
  unfold probedBody RestartAttemptAccounting.countedBody RestartAttemptAccounting.traceBody
    bodySite RestartAttemptAccounting.attemptIncrement Operations.lessThan
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
    Arlib.Computation.Charged.val_op, decide_eq_true_eq,
    Bool.false_eq_true, if_false, and_true, if_pos hallow, Option.none_or]
  cases hcs : (chainStep r o₁ o₂ tape s.drawTrials q w current.state current.bitCursor).val with
  | none => simp
  | some result =>
    obtain ⟨state, bitCursor⟩ := result
    simp only [Arlib.Computation.Charged.val_bind]
    cases hk : (classifyState state).val with
    | invalid => simp [Operations.successor, Arlib.Computation.Charged.val_op]
    | transversal => simp [Operations.successor, Arlib.Computation.Charged.val_op]
    | defect i j => simp [Operations.successor, Arlib.Computation.Charged.val_op]







/-- INTERNAL: A dead or already-done accumulator leaves the whole scan value
unchanged, on every tape. -/
theorem probedBody_scan_frozen_val {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (xs : List ℕ) (st : Option (RestartCursor n))
    (done : Bool) (count : ℕ) (hfr : st = none ∨ done = true) :
    (Arlib.Computation.Charged.foldlWhile
        (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs
        (((st, done), count), none)).val = (((st, done), count), none) := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    rw [probedBody_scan_cons]
    rcases hfr with hfr | hfr
    · subst hfr
      rw [probedBody_dead]
    · subst hfr
      rw [probedBody_done]





end CountingMatroid.Analysis.RestartDrawProbeScanReplay

end
set_option autoImplicit false

/-!
Interval replay for the concrete ordinal probe's own accumulation, confined
to one capped return scan and lifted through the transition, stage and
restart folds. A captured descriptor can only ever change at the globally
unique attempt whose running count matches the probed ordinal; before that
attempt the probe is silent, and after it the descriptor is sticky.
-/
namespace CountingMatroid.Analysis.RestartDrawProbeScanReplay
end CountingMatroid.Analysis.RestartDrawProbeScanReplay
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartDrawProbeScanReplay
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Analysis.ChainStepIntervalReplay
open CountingMatroid.Analysis.ObservationRoundDrawSites
open CountingMatroid.Analysis.RestartAttemptAccounting

/-- INTERNAL: A return scan that captures nothing and ends live before the
probed ordinal replays its entire value from the bits its successful chain
attempts consumed; no attempt in it can have matched the ordinal.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n) (ordinal : ℕ) (draw : Fin 3) :
    ∀ (xs : List ℕ) (cur : RestartCursor n) (done : Bool) (count floor : ℕ),
      floor ≤ cur.bitCursor → ∀ (tape : ℕ → Bool) (c : RestartCursor n),
      (Arlib.Computation.Charged.foldlWhile
          (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs
          (((some cur, done), count), none)).val.2 = none →
      (Arlib.Computation.Charged.foldlWhile
          (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs
          (((some cur, done), count), none)).val.1.1.1 = some c →
      (Arlib.Computation.Charged.foldlWhile
          (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs
          (((some cur, done), count), none)).val.1.2 ≤ ordinal →
      floor ≤ c.bitCursor ∧ ∀ other : ℕ → Bool,
        (∀ i, floor ≤ i → i < c.bitCursor → tape i = other i) →
        (Arlib.Computation.Charged.foldlWhile
          (fun acc (_ : ℕ) => probedBody r o₁ o₂ other s q w ordinal draw acc) xs
          (((some cur, done), count), none)).val =
        (Arlib.Computation.Charged.foldlWhile
          (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs
          (((some cur, done), count), none)).val := by
  intro xs
  induction xs with
  | nil =>
    intro cur done count floor hfl tape c _ hc _
    rw [Arlib.Computation.Charged.val_foldlWhile_nil] at hc
    have hc' : cur = c := Option.some.inj hc
    subst hc'
    refine ⟨hfl, fun other _ => ?_⟩
    rw [Arlib.Computation.Charged.val_foldlWhile_nil,
      Arlib.Computation.Charged.val_foldlWhile_nil]
  | cons a xs ih =>
    intro cur done count floor hfl tape c hobs hc hcount
    cases done with
    | true =>
      rw [probedBody_scan_frozen_val r o₁ o₂ tape s q w ordinal draw _ _ true count
        (Or.inr rfl)] at hc
      have hc' : cur = c := Option.some.inj hc
      subst hc'
      refine ⟨hfl, fun other _ => ?_⟩
      rw [probedBody_scan_frozen_val r o₁ o₂ tape s q w ordinal draw _ _ true count
        (Or.inr rfl), probedBody_scan_frozen_val r o₁ o₂ other s q w ordinal draw _ _ true
        count (Or.inr rfl)]
    | false =>
      by_cases hallow : cur.attempts < s.restartCap
      · by_cases hcm : count = ordinal
        · exfalso
          subst hcm
          rw [probedBody_scan_cons, probedBody_eq r o₁ o₂ tape s q w draw cur count
            hallow] at hcount
          cases hcs : (chainStep r o₁ o₂ tape s.drawTrials q w cur.state
              cur.bitCursor).val with
          | none =>
            rw [hcs] at hcount
            simp only at hcount
            have hm := probedBody_scan_count_mono r o₁ o₂ tape s q w count draw xs
              (((none, true), count + 1),
                chainDrawSite r o₁ o₂ tape s q w cur.state cur.bitCursor draw)
            simp only at hm
            omega
          | some result =>
            obtain ⟨state, bitCursor⟩ := result
            rw [hcs] at hcount
            simp only at hcount
            have hm := probedBody_scan_count_mono r o₁ o₂ tape s q w count draw xs
              (((some ⟨state, bitCursor, cur.attempts + 1⟩,
                decide ((classifyState state).val = StateKind.transversal)), count + 1),
                chainDrawSite r o₁ o₂ tape s q w cur.state cur.bitCursor draw)
            simp only at hm
            omega
        · rw [probedBody_scan_cons, probedBody_ne r o₁ o₂ tape s q w ordinal draw cur
            count hallow hcm] at hobs hc hcount
          cases hcs : (chainStep r o₁ o₂ tape s.drawTrials q w cur.state
              cur.bitCursor).val with
          | none =>
            rw [hcs] at hc
            simp only at hc
            rw [probedBody_scan_frozen_val r o₁ o₂ tape s q w ordinal draw xs none true
              (count + 1) (Or.inl rfl)] at hc
            cases hc
          | some result =>
            obtain ⟨state, bitCursor⟩ := result
            rw [hcs] at hobs hc hcount
            simp only at hobs hc hcount
            have hstep := chainStep_success_interval r o₁ o₂ s.drawTrials q w cur.state
              cur.bitCursor tape (state, bitCursor) hcs
            have hr := ih ⟨state, bitCursor, cur.attempts + 1⟩
              (decide ((classifyState state).val = StateKind.transversal)) (count + 1)
              bitCursor (le_refl _) tape c hobs hc hcount
            refine ⟨hfl.trans (hstep.1.trans hr.1), ?_⟩
            intro other hagree
            have heqstep := hstep.2 other (fun i hlo hhi =>
              hagree i (hfl.trans hlo) (hhi.trans_le hr.1))
            have heqrest := hr.2 other (fun i hlo hhi =>
              hagree i (hfl.trans (hstep.1.trans hlo)) hhi)
            beta_reduce at heqstep heqrest ⊢
            rw [probedBody_scan_cons, probedBody_ne r o₁ o₂ other s q w ordinal draw cur
              count hallow hcm, heqstep, probedBody_scan_cons, probedBody_ne r o₁ o₂ tape s q w
              ordinal draw cur count hallow hcm, hcs]
            exact heqrest
      · rw [probedBody_scan_cons, probedBody_refused r o₁ o₂ tape s q w ordinal draw cur
          count hallow] at hc
        simp only at hc
        rw [probedBody_scan_frozen_val r o₁ o₂ tape s q w ordinal draw xs none true
          count (Or.inl rfl)] at hc
        cases hc
