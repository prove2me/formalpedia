-- Prove2me | solution 1 for CountingMatroid.Analysis.TraceReturnIntervalReplay.traceReturn_success_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:57:10.122816+00:00
-- url     : https://prove2.me/submissions/56de9e03-6762-4092-8a69-0e69d8916224

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
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

namespace CountingMatroid.Analysis.TraceReturnIntervalReplay
end CountingMatroid.Analysis.TraceReturnIntervalReplay
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
section


set_option autoImplicit false

/-!
Capped return scans replay from the interval consumed by their successful
underlying chain attempts. The induction retains the return flag, the abort
state, and early termination of the charged foldlWhile scan.
-/

namespace CountingMatroid.Analysis.TraceReturnIntervalReplay
open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ChainStepIntervalReplay

/-- INTERNAL: Expose the value recursion of a charged early-break fold. -/
private theorem foldlWhile_cons_value {α β : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell (Option β))
    (a : α) (xs : List α) (b : β) :
    (Arlib.Computation.Charged.foldlWhile f (a :: xs) b).val =
      match (f b a).val with
      | none => b
      | some next => (Arlib.Computation.Charged.foldlWhile f xs next).val := by
  cases h : (f b a).val <;>
    simp only [Arlib.Computation.Charged.val] at h ⊢ <;>
    simp [Arlib.Computation.Charged.foldlWhile, h]



end CountingMatroid.Analysis.TraceReturnIntervalReplay

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r21 · proved · capped return-scan replay with the return flag retained in
  the induction and absorbing abort states excluded on successful paths.
-/

end
set_option autoImplicit false

/-!
Capped return scans replay from the interval consumed by their successful
underlying chain attempts. The induction retains the return flag, the abort
state, and early termination of the charged foldlWhile scan.
-/

namespace CountingMatroid.Analysis.TraceReturnIntervalReplay
end CountingMatroid.Analysis.TraceReturnIntervalReplay
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.TraceReturnIntervalReplay
open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ChainStepIntervalReplay

/-- INTERNAL: Successful capped positive-time returns have monotone cursors
and replay from the interval consumed by their underlying chain attempts.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (q : ℚ)
    (weights : Multipliers n) (start : RestartCursor n) :
    SuccessReplay (fun tape => (traceReturn r o₁ o₂ tape s q weights start).val)
      RestartCursor.bitCursor start.bitCursor := by
  let body : (ℕ → Bool) → (Option (RestartCursor n) × Bool) → ℕ →
      Arlib.Computation.Charged Op Cell (Option (Option (RestartCursor n) × Bool)) :=
    fun (tape : ℕ → Bool) (acc : Option (RestartCursor n) × Bool) (_ : ℕ) => do
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
  let scan := fun tape xs acc =>
    (Arlib.Computation.Charged.foldlWhile (body tape) xs acc).val
  have hstopped (tape : ℕ → Bool) (xs : List ℕ) (acc : Option (RestartCursor n)) :
      scan tape xs (acc, true) = (acc, true) := by
    cases xs with
    | nil => rfl
    | cons a xs =>
        rw [show scan tape (a :: xs) (acc, true) = _ from foldlWhile_cons_value _ _ _ _]
        rfl
  have hscan : ∀ xs current done,
      SuccessReplay (fun tape =>
        let result := scan tape xs (some current, done)
        result.1.map (fun next => (next, result.2)))
        (fun out => out.1.bitCursor) current.bitCursor := by
    intro xs
    induction xs with
    | nil =>
        intro current done tape out h
        have hout : (current, done) = out := Option.some.inj h
        subst out
        exact ⟨le_rfl, fun _ _ => rfl⟩
    | cons a xs ih =>
        intro current done tape out h
        by_cases hd : done = true
        · subst done
          simp only [hstopped, Option.map_some] at h
          have hout := Option.some.inj h
          subst out
          refine ⟨le_rfl, ?_⟩
          intro other _
          simp only [hstopped, Option.map_some]
        · have hd' : done = false := Bool.eq_false_iff.mpr hd
          subst done
          have hvalue (t : ℕ → Bool) : scan t (a :: xs) (some current, false) =
              match (body t (some current, false) a).val with
              | none => (some current, false)
              | some next => scan t xs next := by
            dsimp only [scan]
            rw [foldlWhile_cons_value]
            cases (body t (some current, false) a).val <;> rfl
          simp only [hvalue, body, Bool.false_eq_true, ite_false,
            Arlib.Computation.Charged.val_bind] at h
          by_cases hallowed : (lessThan current.attempts s.restartCap).val = true
          · rw [if_pos hallowed] at h
            simp only [Arlib.Computation.Charged.val_bind] at h
            cases hstep : (chainStep r o₁ o₂ tape s.drawTrials q weights
                current.state current.bitCursor).val with
            | none =>
                simp only [hstep, Arlib.Computation.Charged.val_pure, hstopped,
                  Option.map_none] at h
                contradiction
            | some step =>
                cases step with
                | mk state stop =>
                  simp only [hstep, Arlib.Computation.Charged.val_bind] at h
                  let returned := match (classifyState state).val with
                    | .transversal => true
                    | _ => false
                  let next : RestartCursor n :=
                    ⟨state, stop, (successor current.attempts).val⟩
                  have hresult : SuccessReplay (fun t =>
                      let result := scan t xs (some next, returned)
                      result.1.map (fun next => (next, result.2)))
                      (fun out => out.1.bitCursor) stop := ih next returned
                  have hrest : (let result := scan tape xs (some next, returned)
                      result.1.map (fun next => (next, result.2))) = some out := by
                    cases hk : (classifyState state).val <;>
                      simpa only [hk, Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure, returned, next] using h
                  have hr := hresult tape out hrest
                  have hs := chainStep_success_interval r o₁ o₂ s.drawTrials q weights
                    current.state current.bitCursor tape (state, stop) hstep
                  refine ⟨hs.1.trans hr.1, ?_⟩
                  intro other hagree
                  have heq := hs.2 other (fun i hlo hhi => hagree i hlo (hhi.trans_le hr.1))
                  have hreplay := hr.2 other (fun i hlo hhi => hagree i (hs.1.trans hlo) hhi)
                  dsimp only at heq
                  simp only [hvalue, body, Bool.false_eq_true, ite_false,
                    Arlib.Computation.Charged.val_bind]
                  rw [if_pos hallowed]
                  simp only [Arlib.Computation.Charged.val_bind, heq]
                  cases hk : (classifyState state).val <;>
                    simpa only [hk, Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure, returned, next] using hreplay
          · rw [if_neg hallowed] at h
            simp only [Arlib.Computation.Charged.val_pure, hstopped, Option.map_none] at h
            contradiction
  intro tape out hrun
  unfold traceReturn at hrun ⊢
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.repeatWhile] at hrun ⊢
  change (if (scan tape (List.range s.restartCap) (some start, false)).2 then
    pure (scan tape (List.range s.restartCap) (some start, false)).1 else pure none : Arlib.Computation.Charged Op Cell (Option (RestartCursor n))).val = some out at hrun
  by_cases hdone : (scan tape (List.range s.restartCap) (some start, false)).2 = true
  · rw [if_pos hdone] at hrun
    have hlocal := hscan (List.range s.restartCap) start false tape (out, true) (by
      dsimp only
      simp only [show (scan tape (List.range s.restartCap) (some start, false)).1 = some out from hrun,
        hdone, Option.map_some])
    refine ⟨hlocal.1, ?_⟩
    intro other hagree
    have heq := hlocal.2 other hagree
    dsimp only at heq
    cases hh : scan other (List.range s.restartCap) (some start, false) with
    | mk value done =>
      cases value with
      | none => simp only [hh, Option.map_none] at heq; contradiction
      | some result =>
        simp only [hh, Option.map_some] at heq
        have hout := Option.some.inj heq
        have hr : result = out := congrArg Prod.fst hout
        have hd : done = true := congrArg Prod.snd hout
        change (if (scan other (List.range s.restartCap) (some start, false)).2 then
          pure (scan other (List.range s.restartCap) (some start, false)).1 else pure none : Arlib.Computation.Charged Op Cell (Option (RestartCursor n))).val = some out
        simp only [hh, hd, ite_true, hr, Arlib.Computation.Charged.val_pure]
  · rw [if_neg hdone] at hrun
    cases hrun
