-- Prove2me | solution 1 for FiniteMagmaE677.op_eq_of_e677_rows_agree
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-20T22:48:52.672859+00:00
-- url     : https://prove2.me/submissions/fc627f64-cf64-418d-a480-0a454b912c1c

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_FiniteMagmaE677
import Mathlib

/-!
# Support rule for two `E677` tables

Let `op` (old) and `op'` (new) be two operations on the same finite carrier, both satisfying
`E677`. If rows `b` and `t` are the same in both tables and `op b t = a`, then
`op' a b = op a b`.

Proof: old `E677` at `(t, b)` reads `t = op b (op t (op a b))`. New `E677` at `(t, b)`, with rows
`b`, `t` unchanged and `op b t = a`, reads `t = op b (op t (op' a b))`. Cancel row `b`, then
row `t`, in the old table. Left cancellation holds because every row of a finite `E677` table is
surjective (by `E677` itself), hence injective.
-/

universe u
open FiniteMagmaE677

namespace RowRigidityHelpers

variable {α : Type u}

/-- Left multiplication by `y` is surjective in an `E677` table: `x = op y (op x (op (op y x) y))`.
-/
private theorem leftMul_surj {op : α → α → α} (h : E677 op) (y : α) :
    Function.Surjective (op y) :=
  fun x ↦ ⟨op x (op (op y x) y), (h x y).symm⟩

/-- Left cancellation in a finite `E677` table. -/
private theorem left_cancel [Finite α] {op : α → α → α} (h : E677 op) (y : α) {a b : α}
    (hab : op y a = op y b) : a = b :=
  Finite.injective_iff_surjective.mpr (leftMul_surj h y) hab

end RowRigidityHelpers

theorem solution
{α : Type u} [Finite α] (op op' : α → α → α)
(h : FiniteMagmaE677.E677 op) (h' : FiniteMagmaE677.E677 op') (a b t : α)
(hb : ∀ y : α, op' b y = op b y) (ht : ∀ y : α, op' t y = op t y)
(hbt : op b t = a) :
op' a b = op a b := by
  have hold : t = op b (op t (op a b)) := by
    have h0 := h t b
    rwa [hbt] at h0
  have hnew : t = op b (op t (op' a b)) := by
    have h0 := h' t b
    rwa [hb t, hbt, ht, hb] at h0
  exact RowRigidityHelpers.left_cancel h t
    (RowRigidityHelpers.left_cancel h b (hnew.symm.trans hold))

#print axioms solution
