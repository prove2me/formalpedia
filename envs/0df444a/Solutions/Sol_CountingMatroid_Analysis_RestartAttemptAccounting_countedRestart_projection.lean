-- Prove2me | solution 1 for CountingMatroid.Analysis.RestartAttemptAccounting.countedRestart_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:23:35.96234+00:00
-- url     : https://prove2.me/submissions/a7265dfb-7cf4-4dde-9fa6-aebd12fcb9cc

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
import Theorems.Thm_CountingMatroid_Analysis_RestartAttemptAccounting_countedReturn_projection

namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
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
Value-preserving restart instrumentation. The auxiliary natural number counts
only calls to `chainStep`; it survives both draw aborts and attempt-cap aborts.
It uses the original charged operations and the original tape. It establishes
no probabilistic bound and constructs no draw histories.
-/
namespace CountingMatroid.Analysis.RestartAttemptAccounting

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program















/-- INTERNAL: Forgetting an auxiliary counter also commutes with a fixed loop. -/
private theorem fold_projection {α β γ : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell β)
    (g : (β × γ) → α → Arlib.Computation.Charged Op Cell (β × γ))
    (h : ∀ b c a, (g (b,c) a).val.1 = (f b a).val)
    (xs : List α) (b : β) (c : γ) :
    (Arlib.Computation.Charged.foldl g xs (b,c)).val.1 =
      (Arlib.Computation.Charged.foldl f xs b).val := by
  induction xs generalizing b c with
  | nil => rfl
  | cons a xs ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons,
        Arlib.Computation.Charged.val_foldl_cons]
      have hi := ih (g (b,c) a).val.1 (g (b,c) a).val.2
      rw [← h b c a]
      exact hi







/-- INTERNAL: Stage instrumentation projects to the original nested trace loop. -/
private theorem stage_projection {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (index : ℕ) (acc : Option (RestartCursor n)) (count : ℕ) :
    (countedStage r o₁ o₂ tape s tables index (acc,count)).val.1 =
    (do match acc with
      | none => pure none
      | some current =>
          let a ← successor index
          let q ← ratPower s.ρ a
          let w ← learnedWeightRead tables a s.L
          Arlib.Computation.Charged.repeatFor (fun _ acc => do
            match acc with
            | none => pure none
            | some current => traceReturn r o₁ o₂ tape s q w current)
            s.τ (some current) :
        Arlib.Computation.Charged Op Cell (Option (RestartCursor n))).val := by
  have hp (q : ℚ) (w : Multipliers n) := fold_projection
    (fun acc (_ : ℕ) => match acc with
      | none => pure none
      | some current => traceReturn r o₁ o₂ tape s q w current)
    (fun acc (_ : ℕ) => countedTransition r o₁ o₂ tape s q w acc)
    (by intro b c a; cases b <;> simp only [countedTransition,
      Arlib.Computation.Charged.val_pure, countedReturn_projection])
    (List.range s.τ) acc count
  cases acc <;> simp only [countedStage, Arlib.Computation.Charged.val_bind,
    successor, ratPower, learnedWeightRead, Arlib.Computation.Charged.val_op,
    Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.repeatFor, hp]
  · have hz (xs : List ℕ) :
        (Arlib.Computation.Charged.foldl (fun (acc : Option (RestartCursor n)) (_ : ℕ) =>
          match acc with
          | none => pure none
          | some current => traceReturn r o₁ o₂ tape s
              (ratPower s.ρ (index + 1)).val
              (learnedWeightRead tables (index + 1) s.L).val current) xs none).val = none := by
        induction xs with
        | nil => rfl
        | cons a xs ih => simpa only [Arlib.Computation.Charged.val_foldl_cons,
            Arlib.Computation.Charged.val_pure] using ih
    exact hz (List.range s.τ)









end CountingMatroid.Analysis.RestartAttemptAccounting

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · instrumented the actual guarded trace body and nested restart; projection preserves every public value, while the independent attempt counter survives abort. Packaged the existing reached-prefix witness.
-/

end
set_option autoImplicit false

/-!
Value-preserving restart instrumentation. The auxiliary natural number counts
only calls to `chainStep`; it survives both draw aborts and attempt-cap aborts.
It uses the original charged operations and the original tape. It establishes
no probabilistic bound and constructs no draw histories.
-/
namespace CountingMatroid.Analysis.RestartAttemptAccounting
end CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartAttemptAccounting

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: The complete counted restart has exactly the original result.
The additional count, unlike `RestartCursor.attempts`, survives an abort. -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor : ℕ) :
    (countedRestart r o₁ o₂ tape s tables j cursor).val.1 =
      (restartPhase r o₁ o₂ tape s tables j cursor).val := by
  have hp := fold_projection
    (fun acc index => do match acc with
      | none => pure none
      | some current =>
          let a ← successor index
          let q ← ratPower s.ρ a
          let w ← learnedWeightRead tables a s.L
          Arlib.Computation.Charged.repeatFor (fun _ acc => do
            match acc with
            | none => pure none
            | some current => traceReturn r o₁ o₂ tape s q w current)
            s.τ (some current))
    (fun acc index => countedStage r o₁ o₂ tape s tables index acc)
    (fun b c a => stage_projection r o₁ o₂ tape s tables a b c)
    (List.range j)
    (some ⟨(freshTransversal n tape cursor).val.1,
      (freshTransversal n tape cursor).val.2, 0⟩) 0
  simp only [countedRestart, restartPhase, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.repeatFor]
  rw [hp]
  simp only [Arlib.Computation.Charged.repeatFor] at hp ⊢
  have project (result : Option (RestartCursor n)) :
      result.map (fun current => (current.state, current.bitCursor)) =
        (match result with
        | none => pure none
        | some current => pure (some (current.state, current.bitCursor)) :
          Arlib.Computation.Charged Op Cell (Option (PairedSet n × ℕ))).val := by
    cases result <;> rfl
  exact project _
