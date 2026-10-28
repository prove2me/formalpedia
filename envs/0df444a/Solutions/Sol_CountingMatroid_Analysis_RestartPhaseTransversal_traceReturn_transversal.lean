-- Prove2me | solution 1 for CountingMatroid.Analysis.RestartPhaseTransversal.traceReturn_transversal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:06:57.598766+00:00
-- url     : https://prove2.me/submissions/22fb4a7b-0d62-4e6d-b8e6-faba89d530cd

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
section


set_option autoImplicit false

/-!
Every successful capped return ends in the transversal class. Consequently
successful restarts return a transversal, including phases with no crossed
levels or no trace transitions. These are deterministic operational facts;
they make no probability or finite-tape coverage claim.
-/

namespace CountingMatroid.Analysis.RestartPhaseTransversal

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: An early-break charged fold preserves an invariant when each
continuing step preserves it. -/
private theorem foldWhile_preserves {α β : Type} (P : β → Prop)
    (f : β → α → Arlib.Computation.Charged Op Cell (Option β))
    (hstep : ∀ b a next, P b → (f b a).val = some next → P next)
    (xs : List α) (b : β) (hb : P b) :
    P (Arlib.Computation.Charged.foldlWhile f xs b).val := by
  induction xs generalizing b with
  | nil => exact hb
  | cons a xs ih =>
      have hrec : (Arlib.Computation.Charged.foldlWhile f (a :: xs) b).val =
          match (f b a).val with
          | none => b
          | some next => (Arlib.Computation.Charged.foldlWhile f xs next).val := by
        cases h : (f b a).val <;>
          simp only [Arlib.Computation.Charged.val] at h ⊢ <;>
          simp [Arlib.Computation.Charged.foldlWhile, h]
      rw [hrec]
      cases h : (f b a).val with
      | none => exact hb
      | some next => exact ih next (hstep b a next hb h)







end CountingMatroid.Analysis.RestartPhaseTransversal

end
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

/-- INTERNAL: A successful positive-time return has actually reached the
transversal classifier branch, regardless of its initial state.
TEXLINE: main.tex:1163-1176 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (start result : RestartCursor n)
    (h : (traceReturn r o₁ o₂ tape s q weights start).val = some result) :
    (classifyState result.state).val = .transversal := by
  let P : Option (RestartCursor n) × Bool → Prop := fun acc =>
    ∀ current, acc.1 = some current → acc.2 = true →
      (classifyState current.state).val = .transversal
  let body : ℕ → (Option (RestartCursor n) × Bool) →
      Arlib.Computation.Charged Op Cell (Option (Option (RestartCursor n) × Bool)) :=
    fun (_ : ℕ) (acc : Option (RestartCursor n) × Bool) => do
    if acc.2 then pure none
    else
      match acc.1 with
      | none => pure none
      | some current =>
          let allowed ← lessThan current.attempts s.restartCap
          if allowed then
            let attempted ← chainStep r o₁ o₂ tape s.drawTrials q weights
              current.state current.bitCursor
            let attempts ← successor current.attempts
            match attempted with
            | none => pure (some (none, true))
            | some (state, bitCursor) =>
                let kind ← classifyState state
                let returned ← match kind with
                  | .transversal => pure true
                  | _ => pure false
                pure (some (some ⟨state, bitCursor, attempts⟩, returned))
          else pure (some (none, true))
  have hstep : ∀ acc i next, P acc → (body i acc).val = some next → P next := by
    intro acc i next hp hn
    dsimp only [body] at hn
    split at hn
    · cases hn
    · split at hn
      · cases hn
      · simp only [Arlib.Computation.Charged.val_bind] at hn
        split at hn
        · simp only [Arlib.Computation.Charged.val_bind] at hn
          split at hn
          · have heq := Option.some.inj hn
            subst next
            intro current hc _
            cases hc
          · rename_i state cursor _
            simp only [Arlib.Computation.Charged.val_bind] at hn
            cases hk : (classifyState state).val <;>
              simp only [hk, Arlib.Computation.Charged.val_pure] at hn
            all_goals
              have heq := Option.some.inj hn
              subst next
              intro current hc hd
              have hcurrent := Option.some.inj hc
              subst current
            · exact hk
            · cases hd
            · cases hd
        · have heq := Option.some.inj hn
          subst next
          intro current hc _
          cases hc
  have hscan := foldWhile_preserves P (fun acc i => body i acc) hstep
    (List.range s.restartCap) (some start, false) (by
      intro current _ hd
      cases hd)
  unfold traceReturn at h
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.repeatWhile] at h
  change (if (Arlib.Computation.Charged.foldlWhile (fun acc i => body i acc)
    (List.range s.restartCap) (some start, false)).val.2 then
    pure (Arlib.Computation.Charged.foldlWhile (fun acc i => body i acc)
      (List.range s.restartCap) (some start, false)).val.1
    else pure none : Arlib.Computation.Charged Op Cell (Option (RestartCursor n))).val =
      some result at h
  split at h
  · rename_i hd
    exact hscan result h hd
  · cases h
