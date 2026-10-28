-- Prove2me | solution 1 for CountingMatroid.Analysis.ObservationRoundDrawSites.observation_round_draw_sites
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:31:19.126744+00:00
-- url     : https://prove2.me/submissions/be3f7be0-bd61-4283-96de-595815c3ec75

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
import Definitions.Def_CountingMatroid_Analysis_ObservationRoundDrawSites
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
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
import Theorems.Thm_CountingMatroid_Analysis_ChainStepNoninvalid_chainStep_noninvalid
import Theorems.Thm_CountingMatroid_Analysis_ObservationRoundDrawSites_appended_tape_agreement
import Theorems.Thm_CountingMatroid_Analysis_ObservationRoundDrawSites_chainDrawSite_success_interval
import Theorems.Thm_CountingMatroid_Analysis_ObservationRoundDrawSites_chain_abort_draw_site
import Theorems.Thm_CountingMatroid_Analysis_ObservePhaseIntervalReplay_observePhase_success_interval
import Theorems.Thm_CountingMatroid_Analysis_RestartPhaseIntervalReplay_restartPhase_success_interval
import Theorems.Thm_CountingMatroid_Analysis_RestartPhaseTransversal_restartPhase_transversal
import Theorems.Thm_CountingMatroid_Analysis_SinglePhaseIntervalReplay_single_phase_interval_replay
import Theorems.Thm_CountingMatroid_Analysis_SuccessfulPhaseReplay_successful_history_replay_of_phase_replay

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
namespace CountingMatroid.Analysis.SuccessfulPhaseReplay
end CountingMatroid.Analysis.SuccessfulPhaseReplay
namespace CountingMatroid.Analysis.SinglePhaseIntervalReplay
end CountingMatroid.Analysis.SinglePhaseIntervalReplay
namespace CountingMatroid.Analysis.RestartPhaseIntervalReplay
end CountingMatroid.Analysis.RestartPhaseIntervalReplay
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
namespace CountingMatroid.Analysis.ChainStepNoninvalid
end CountingMatroid.Analysis.ChainStepNoninvalid
namespace CountingMatroid.Analysis.RestartPhaseTransversal
end CountingMatroid.Analysis.RestartPhaseTransversal
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.RationalHeight



/-- INTERNAL: A charged finite loop preserves any invariant preserved by its body. -/
theorem chargedFold_preserves {ι β : Type} (P : β → Prop)
    (f : β → ι → Arlib.Computation.Charged Op Cell β)
    (hf : ∀ b i, P b → P (f b i).val) (l : List ι) (b : β) (hb : P b) :
    P (Arlib.Computation.Charged.foldl f l b).val := by
  induction l generalizing b with
  | nil => simpa using hb
  | cons i xs ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons]
      exact ih _ (hf b i hb)





















end CountingMatroid.Analysis.BoundedRunResourceEnvelope

end

section


set_option autoImplicit false

/-!
The three stopped draw descriptors of one actual observation attempt. Each
descriptor records an absolute bit cursor and the actual draw denominator.
History, restart, and observation replay compose with the chain-level
stopped-draw replay and abort-attribution invariants. The independent
selector correctness proof is isolated in a child module; trial coverage remains
a separate quantitative obligation.
-/

namespace CountingMatroid.Analysis.ObservationRoundDrawCover
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment



end CountingMatroid.Analysis.ObservationRoundDrawCover

namespace CountingMatroid.Analysis.ObservationRoundDrawSites

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.ObservationRoundDrawCover





/-- INTERNAL: Recording the initial transversal cannot abort and draws
no chain bits; the observation loop with one observation therefore succeeds.
TEXLINE: main.tex:1177-1187 -/
private theorem observePhase_first_not_none {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (start : PairedSet n × ℕ)
    (htransversal : (classifyState start.1).val = .transversal) :
    (observePhase r o₁ o₂ tape {s with observations := 1} q weights start).val ≠ none := by
  simp only [observePhase, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.repeatFor, List.range_one,
    Arlib.Computation.Charged.val_foldl_cons, Arlib.Computation.Charged.val_foldl_nil,
    Model.Operations.natEqual, Arlib.Computation.Charged.val_op,
    beq_self_eq_true, ite_true]
  simp only [recordObservation, Arlib.Computation.Charged.val_bind,
    htransversal, Arlib.Computation.Charged.val_pure]
  intro hfail
  cases hfail

/-- INTERNAL: A successful record certifies a non-invalid state. -/
private theorem recordObservation_success_noninvalid {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (rho : ℚ) (current next : ObservationCursor n)
    (h : (recordObservation r o₁ o₂ rho current).val = some next) :
    (classifyState next.state).val ≠ .invalid := by
  unfold recordObservation at h
  simp only [Arlib.Computation.Charged.val_bind] at h
  cases hk : (classifyState current.state).val with
  | invalid => simp only [hk, Arlib.Computation.Charged.val_pure, reduceCtorEq] at h
  | transversal =>
      simp only [hk, Arlib.Computation.Charged.val_bind] at h
      cases (Option.some.inj h).symm
      rw [hk]
      intro hbad
      cases hbad
  | defect i j =>
      simp only [hk, Arlib.Computation.Charged.val_bind] at h
      cases (Option.some.inj h).symm
      rw [hk]
      intro hbad
      cases hbad

/-- INTERNAL: The successful observation prefix retains a non-invalid state,
including a zero-length prefix of a valid restart endpoint. -/
private theorem observePhase_success_noninvalid {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (start : PairedSet n × ℕ) (reached : ObservationCursor n)
    (hstart : (classifyState start.1).val ≠ .invalid)
    (h : (observePhase r o₁ o₂ tape s q weights start).val = some reached) :
    (classifyState reached.state).val ≠ .invalid := by
  let P : Option (ObservationCursor n) → Prop := fun outcome =>
    ∀ current, outcome = some current → (classifyState current.state).val ≠ .invalid
  let step : Option (ObservationCursor n) → ℕ →
      Arlib.Computation.Charged Model.Operations.Op Model.Operations.Cell
        (Option (ObservationCursor n)) := fun outcome index => do
    match outcome with
    | none => pure none
    | some current =>
        let onStart ← Model.Operations.natEqual index 0
        if onStart then recordObservation r o₁ o₂ s.ρ current
        else
          let next ← chainStep r o₁ o₂ tape s.drawTrials q weights
            current.state current.bitCursor
          match next with
          | none => pure none
          | some (state, bitCursor) =>
              recordObservation r o₁ o₂ s.ρ
                ⟨state, bitCursor, current.counts, current.numeratorSum⟩
  have hstep : ∀ outcome index, P outcome → P (step outcome index).val := by
    intro outcome index _ next hn
    cases outcome with
    | none => cases hn
    | some current =>
        dsimp only [step] at hn
        simp only [Arlib.Computation.Charged.val_bind] at hn
        split at hn
        · exact recordObservation_success_noninvalid r o₁ o₂ s.ρ current next hn
        · simp only [Arlib.Computation.Charged.val_bind] at hn
          split at hn
          · cases hn
          · exact recordObservation_success_noninvalid r o₁ o₂ s.ρ _ next hn
  let initial : ObservationCursor n := ⟨start.1, start.2, (Model.Operations.allocateCounts n).val, 0⟩
  have hi : P (some initial) := by
    intro current hc
    cases (Option.some.inj hc).symm
    exact hstart
  have hfold := BoundedRunResourceEnvelope.chargedFold_preserves P step hstep
    (List.range s.observations) (some initial) hi
  change (Arlib.Computation.Charged.foldl step (List.range s.observations)
    (some initial)).val = some reached at h
  exact hfold reached h

/-- INTERNAL: The next noninitial observation can abort only through its
chain attempt, once the reached prefix state is non-invalid. -/
private theorem observation_next_abort_chain_none {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (start : PairedSet n × ℕ) (k : ℕ) (reached : ObservationCursor n)
    (hk : k ≠ 0) (hvalid : (classifyState reached.state).val ≠ .invalid)
    (ho : (observePhase r o₁ o₂ tape {s with observations := k} q weights start).val = some reached)
    (hf : (observePhase r o₁ o₂ tape {s with observations := k + 1} q weights start).val = none) :
    (chainStep r o₁ o₂ tape s.drawTrials q weights reached.state reached.bitCursor).val = none := by
  let step : Option (ObservationCursor n) → ℕ →
      Arlib.Computation.Charged Model.Operations.Op Model.Operations.Cell
        (Option (ObservationCursor n)) := fun outcome index => do
    match outcome with
    | none => pure none
    | some current =>
        let onStart ← Model.Operations.natEqual index 0
        if onStart then recordObservation r o₁ o₂ s.ρ current
        else
          let next ← chainStep r o₁ o₂ tape s.drawTrials q weights
            current.state current.bitCursor
          match next with
          | none => pure none
          | some (state, bitCursor) =>
              recordObservation r o₁ o₂ s.ρ
                ⟨state, bitCursor, current.counts, current.numeratorSum⟩
  have happend (xs ys : List ℕ) (initial : Option (ObservationCursor n)) :
      (Arlib.Computation.Charged.foldl step (xs ++ ys) initial).val =
      (Arlib.Computation.Charged.foldl step ys
        (Arlib.Computation.Charged.foldl step xs initial).val).val := by
    induction xs generalizing initial with
    | nil => rfl
    | cons i xs ih =>
        simpa only [List.cons_append, Arlib.Computation.Charged.val_foldl_cons] using
          ih (step initial i).val
  let initial : ObservationCursor n := ⟨start.1, start.2, (Model.Operations.allocateCounts n).val, 0⟩
  change (Arlib.Computation.Charged.foldl step (List.range k) (some initial)).val = some reached at ho
  change (Arlib.Computation.Charged.foldl step (List.range (k + 1)) (some initial)).val = none at hf
  rw [List.range_succ, happend, ho, Arlib.Computation.Charged.val_foldl_cons,
    Arlib.Computation.Charged.val_foldl_nil] at hf
  dsimp only [step] at hf
  simp only [Arlib.Computation.Charged.val_bind, Model.Operations.natEqual,
    Arlib.Computation.Charged.val_op, beq_eq_false_iff_ne.mpr hk, Bool.false_eq_true,
    ite_false] at hf
  cases hc : (chainStep r o₁ o₂ tape s.drawTrials q weights reached.state reached.bitCursor).val with
  | none => rfl
  | some next =>
      cases next with
      | mk state cursor =>
          simp only [hc] at hf
          have hnext := ChainStepNoninvalid.chainStep_noninvalid r o₁ o₂ tape
            s.drawTrials q weights reached.state reached.bitCursor (state, cursor) hvalid hc
          unfold recordObservation at hf
          simp only [Arlib.Computation.Charged.val_bind] at hf
          cases hkind : (classifyState state).val <;>
            simp only [hkind, Arlib.Computation.Charged.val_bind,
              Arlib.Computation.Charged.val_pure, reduceCtorEq] at hf
          exact False.elim (hnext hkind)





end CountingMatroid.Analysis.ObservationRoundDrawSites

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r28 · proved · closed observation_round_draw_sites with proved stopped-draw replay, sampler range, classifier weight, and selector correctness helpers; preserved the statement and every original import. Both live handoffs were mechanically rejected without diagnostic, so all child proofs were completed vertically.
* r28 · narrowed · after mechanical rejection of r28-observation-draw-sites-1 without diagnostic, proved the chain replay and abort-attribution children; isolated the remaining classifier-valid selection population/count bridge in ClassifiedStateSelection.
* r28 · composed · removed the parent’s local proof gaps by composing history, restart, observation and stopped-chain replay; attributed reached aborts using the independent chain abort helper. Both child statements elaborate; their chain-level proofs are prepared for the live OPEN handoff.
* r27 · decomposed · defined the three pre-draw stopping descriptors; attempted prefix replay and abort attribution, exposing the n-element-state/selection and stopping-locality obligations separately from trial coverage.
-/

end
set_option autoImplicit false

/-!
The three stopped draw descriptors of one actual observation attempt. Each
descriptor records an absolute bit cursor and the actual draw denominator.
History, restart, and observation replay compose with the chain-level
stopped-draw replay and abort-attribution invariants. The independent
selector correctness proof is isolated in a child module; trial coverage remains
a separate quantitative obligation.
-/

namespace CountingMatroid.Analysis.ObservationRoundDrawCover
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment



end CountingMatroid.Analysis.ObservationRoundDrawCover

namespace CountingMatroid.Analysis.ObservationRoundDrawSites
end CountingMatroid.Analysis.ObservationRoundDrawSites
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ObservationRoundDrawSites

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.ObservationRoundDrawCover

/-- INTERNAL: Actual stopped draw sites are local in their consumed prefixes,
and a reached round abort is attributable to one of those three capped draws.
Trial widths and the finite-block bound are not conclusions of this lemma.
TEXLINE: main.tex:1177-1187,1392-1421 -/
theorem solution (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref)
    (k : ℕ) (hk : k < (CountingMatroid.Interface.Pseudocode.setup n p).observations) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    (∀ site suffix, suffix.length = t → ∀ d,
      observationDrawSite n r o₁ o₂ p j pref k site suffix = some d →
      ∀ other, other.length = t → suffix.take (d.1 - pref.length) <+: other →
        observationDrawSite n r o₁ o₂ p j pref k site other = some d) ∧
    (∀ suffix, suffix.length = t →
      ReachedObservationRoundAbort n r o₁ o₂ p j pref k suffix →
      ∃ site d, observationDrawSite n r o₁ o₂ p j pref k site suffix = some d ∧
        (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
          s.drawTrials d.2 d.1).val.1 = none) := by
  classical
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  constructor
  · intro site suffix hlen d hsite other hother htake
    -- Replay the history using successful_history_replay_of_phase_replay
    -- and single_phase_interval_replay, then restartPhase_success_interval,
    -- observePhase_success_interval, and the preceding index draws.
    -- The map stops BEFORE this draw, so its descriptor must be stable
    -- under agreement below d.1, not below the end of its capped trials.
    unfold observationDrawSite at hsite
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hsite
    obtain ⟨current, hhistory, start, hrestart, reached, hobserve, hdraw⟩ := hsite
    have hhistoryReplay := SuccessfulPhaseReplay.successful_history_replay_of_phase_replay
      r o₁ o₂ s (SinglePhaseIntervalReplay.single_phase_interval_replay r o₁ o₂ s)
      (fun i => ((pref ++ suffix)[i]?).getD false) j current hhistory
      (fun i => ((pref ++ other)[i]?).getD false)
    have hrestartReplay := RestartPhaseIntervalReplay.restartPhase_success_interval
      r o₁ o₂ s current.tables j current.bitCursor
      (fun i => ((pref ++ suffix)[i]?).getD false) start hrestart
    have hobserveReplay := ObservePhaseIntervalReplay.observePhase_success_interval
      r o₁ o₂ {s with observations := k} (s.ρ ^ j) current.currentWeights start
      (fun i => ((pref ++ suffix)[i]?).getD false) reached hobserve
    split at hdraw
    · cases hdraw
    · rename_i hkzero
      have hdrawReplay := chainDrawSite_success_interval r o₁ o₂ s
        (s.ρ ^ j) current.currentWeights reached.state reached.bitCursor site
        (fun i => ((pref ++ suffix)[i]?).getD false) d hdraw
      have hagree := appended_tape_agreement pref suffix other d.1
        (hlen.trans hother.symm) htake
      have hcurr : current.bitCursor ≤ d.1 :=
        hrestartReplay.1.trans (hobserveReplay.1.trans hdrawReplay.1)
      have hh := hhistoryReplay (fun i hi => hagree i (hi.trans_le hcurr))
      have hs := hrestartReplay.2 (fun i => ((pref ++ other)[i]?).getD false)
        (fun i _ hi => hagree i
          (hi.trans_le (hobserveReplay.1.trans hdrawReplay.1)))
      have ho := hobserveReplay.2 (fun i => ((pref ++ other)[i]?).getD false)
        (fun i _ hi => hagree i (hi.trans_le hdrawReplay.1))
      have hd := hdrawReplay.2 (fun i => ((pref ++ other)[i]?).getD false)
        (fun i _ hi => hagree i hi)
      dsimp only [s] at hh hs ho hd
      unfold observationDrawSite
      simp only [Option.bind_eq_bind, hh, hs, ho, Option.bind_some,
        hkzero, ite_false]
      exact hd

  · intro suffix hlen hbad
    obtain ⟨hprevious, current, hhistory, start, hrestart, reached, hobserve, hfail⟩ := hbad
    have hrestartInterval :=
      RestartPhaseIntervalReplay.restartPhase_success_interval r o₁ o₂ s
        current.tables j current.bitCursor
        (fun i => ((pref ++ suffix)[i]?).getD false) start hrestart
    have hobserveInterval :=
      ObservePhaseIntervalReplay.observePhase_success_interval r o₁ o₂
        {s with observations := k} (s.ρ ^ j) current.currentWeights start
        (fun i => ((pref ++ suffix)[i]?).getD false) reached hobserve
    have htransversal := RestartPhaseTransversal.restartPhase_transversal
      r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false) s current.tables
      j current.bitCursor start hrestart
    by_cases hkzero : k = 0
    · rw [hkzero] at hfail
      exact False.elim ((observePhase_first_not_none r o₁ o₂ _ s (s.ρ ^ j)
        current.currentWeights start htransversal) hfail)
    · have hvalid := observePhase_success_noninvalid r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) {s with observations := k}
        (s.ρ ^ j) current.currentWeights start reached
        (by rw [htransversal]; intro hbad; cases hbad) hobserve
      have hchain := observation_next_abort_chain_none r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s (s.ρ ^ j)
        current.currentWeights start k reached hkzero hvalid hobserve hfail
      obtain ⟨site, d, hsite, hdrawfail⟩ := chain_abort_draw_site r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s (s.ρ ^ j)
        current.currentWeights reached.state reached.bitCursor hvalid hchain
      refine ⟨site, d, ?_, hdrawfail⟩
      unfold observationDrawSite
      simp only [Option.bind_eq_bind, hhistory, hrestart, hobserve,
        Option.bind_some, hkzero, ite_false]
      exact hsite
