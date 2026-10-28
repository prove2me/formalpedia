-- Prove2me | solution 1 for CountingMatroid.Analysis.ChainStepIntervalReplay.foldl_successReplay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:37:13.251131+00:00
-- url     : https://prove2.me/submissions/5bac5172-d39e-4629-95cf-2e46c1e2d413

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
import Theorems.Thm_CountingMatroid_Analysis_ChainStepIntervalReplay_successReplay_bind

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
set_option autoImplicit false

/-!
Success-path replay for the charged chain step. A successful transition has
a monotone cursor and depends only on its consumed bit interval. The generic
option-fold lemma also retains the program's absorbing abort state.
-/

namespace CountingMatroid.Analysis.ChainStepIntervalReplay
end CountingMatroid.Analysis.ChainStepIntervalReplay
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ChainStepIntervalReplay
open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.BoundedUniformReplay

/-- INTERNAL: Lift success-path replay through an option-valued charged fold
whose abort state is absorbing. -/
theorem solution {α β : Type}
    (f : (ℕ → Bool) → Option β → α → Arlib.Computation.Charged Op Cell (Option β))
    (cursor : β → ℕ)
    (hnone : ∀ tape a, (f tape none a).val = none)
    (hstep : ∀ b a, SuccessReplay (fun tape => (f tape (some b) a).val)
      cursor (cursor b)) (xs : List α) (b : β) :
    SuccessReplay (fun tape =>
      (Arlib.Computation.Charged.foldl (f tape) xs (some b)).val) cursor (cursor b) := by
  have habort (tape : ℕ → Bool) (ys : List α) :
      (Arlib.Computation.Charged.foldl (f tape) ys none).val = none := by
    induction ys with
    | nil => rfl
    | cons a ys ih => rw [Arlib.Computation.Charged.val_foldl_cons, hnone, ih]
  induction xs generalizing b with
  | nil =>
      intro tape out h
      have hb := Option.some.inj h
      subst out
      exact ⟨le_rfl, fun _ _ => rfl⟩
  | cons a xs ih =>
      have heq : (fun tape =>
          (Arlib.Computation.Charged.foldl (f tape) (a :: xs) (some b)).val) =
          (fun tape => ((f tape (some b) a).val).bind (fun middle =>
            (Arlib.Computation.Charged.foldl (f tape) xs (some middle)).val)) := by
        funext tape
        rw [Arlib.Computation.Charged.val_foldl_cons]
        cases hs : (f tape (some b) a).val with
        | none => exact habort tape xs
        | some middle => rfl
      rw [heq]
      exact successReplay_bind _ _ cursor cursor (cursor b) (hstep b a) ih
