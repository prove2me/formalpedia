-- Prove2me | solution 1 for CountingMatroid.Analysis.RestartPhaseTransversal.restartPhase_transversal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:39:37.764993+00:00
-- url     : https://prove2.me/submissions/cc34968d-c6c4-44cd-a87b-fb7be9e66d3d

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
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_Analysis_RestartPhaseTransversal_freshTransversal_transversal
import Theorems.Thm_CountingMatroid_Analysis_RestartPhaseTransversal_traceReturn_transversal

namespace CountingMatroid.Analysis.RestartPhaseTransversal
end CountingMatroid.Analysis.RestartPhaseTransversal
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
set_option autoImplicit false

/-!
Every successful capped return ends in the transversal class. Consequently
successful restarts return a transversal, including phases with no crossed
levels or no trace transitions. These are deterministic operational facts;
they make no probability or finite-tape coverage claim.
-/

namespace CountingMatroid.Analysis.RestartPhaseTransversal
end CountingMatroid.Analysis.RestartPhaseTransversal
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartPhaseTransversal

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: Every successful actual phase restart returns a transversal;
empty crossed-stage and trace loops retain the fresh transversal.
TEXLINE: main.tex:1163-1176 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (j cursor : ℕ)
    (result : PairedSet n × ℕ)
    (h : (restartPhase r o₁ o₂ tape s tables j cursor).val = some result) :
    (classifyState result.1).val = .transversal := by
  let P : Option (RestartCursor n) → Prop := fun outcome =>
    ∀ current, outcome = some current →
      (classifyState current.state).val = .transversal
  have hfold (f : Option (RestartCursor n) → ℕ →
      Arlib.Computation.Charged Op Cell (Option (RestartCursor n)))
      (hf : ∀ current i, P current → P (f current i).val)
      (xs : List ℕ) (current : Option (RestartCursor n)) (hc : P current) :
      P (Arlib.Computation.Charged.foldl f xs current).val := by
    induction xs generalizing current with
    | nil => exact hc
    | cons i xs ih =>
        rw [Arlib.Computation.Charged.val_foldl_cons]
        exact ih _ (hf current i hc)
  let stage : Option (RestartCursor n) → ℕ →
      Arlib.Computation.Charged Op Cell (Option (RestartCursor n)) :=
    fun current index => do
      match current with
      | none => pure none
      | some current =>
          let a ← successor index
          let q ← ratPower s.ρ a
          let weights ← learnedWeightRead tables a s.L
          Arlib.Computation.Charged.repeatFor (fun _ current => do
            match current with
            | none => pure none
            | some current => traceReturn r o₁ o₂ tape s q weights current)
            s.τ (some current)
  have hstage : ∀ current i, P current → P (stage current i).val := by
    intro current i hp
    cases current with
    | none => intro next hn; cases hn
    | some current =>
        dsimp only [stage]
        simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.repeatFor]
        apply hfold
        · intro outcome a _ next hn
          cases outcome with
          | none => cases hn
          | some previous => exact traceReturn_transversal r o₁ o₂ tape s _ _ previous next hn
        · exact hp
  let initial : RestartCursor n :=
    ⟨(freshTransversal n tape cursor).val.1, (freshTransversal n tape cursor).val.2, 0⟩
  have hinitial : P (some initial) := by
    intro current hc
    have heq := Option.some.inj hc
    subst current
    exact freshTransversal_transversal n tape cursor
  have hcross := hfold stage hstage (List.range j) (some initial) hinitial
  unfold restartPhase at h
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.repeatFor] at h
  change (match (Arlib.Computation.Charged.foldl stage (List.range j) (some initial)).val with
    | none => pure none
    | some next => pure (some (next.state, next.bitCursor)) :
      Arlib.Computation.Charged Op Cell (Option (PairedSet n × ℕ))).val = some result at h
  cases hc : (Arlib.Computation.Charged.foldl stage (List.range j) (some initial)).val with
  | none => simp only [hc, Arlib.Computation.Charged.val_pure] at h; cases h
  | some next =>
      simp only [hc, Arlib.Computation.Charged.val_pure] at h
      have heq := Option.some.inj h
      subst result
      exact hcross next hc
