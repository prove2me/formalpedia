-- Prove2me | solution 1 for FiniteMagmaE677.collision_cancel
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T06:54:35.103389+00:00
-- url     : https://prove2.me/submissions/1ce7b29f-2444-426a-9761-70f4f18aea17

import Definitions.Def_FiniteMagmaE677
import Theorems.Thm_FiniteMagmaE677_left_bijective
import Theorems.Thm_FiniteMagmaE677_backward_recurrence

/-!
# Cancellation identity for right-translation collisions

If two elements `a`, `b` have the same image under right translation by `x`
(`op a x = op b x = ω`), then the backward recurrence at `(x, a)` and `(x, b)`
gives two decompositions of `x` with the same outer left factor `ω`:

  `x = op ω (op (op a ω) a)` and `x = op ω (op (op b ω) b)`.

Cancelling the outer left factor (left translations are injective in a finite
magma satisfying E677) yields the identity

  `op (op a ω) a = op (op b ω) b`.

No orbit, fixer, or uniqueness hypothesis on `a` and `b` is needed.
-/

universe u

theorem FiniteMagmaE677.collision_cancel {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x a b : α)
    (hcol : op a x = op b x) :
    op (op a (op a x)) a = op (op b (op a x)) b := by
  have hbr1 := FiniteMagmaE677.backward_recurrence op h x a
  have hbr2 := FiniteMagmaE677.backward_recurrence op h x b
  have hinj := (FiniteMagmaE677.left_bijective op h (op a x)).1
  apply hinj
  calc op (op a x) (op (op a (op a x)) a)
      = x := hbr1.symm
    _ = op (op b x) (op (op b (op b x)) b) := hbr2
    _ = op (op a x) (op (op b (op a x)) b) := by rw [hcol]

theorem solution {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x a b : α)
    (hcol : op a x = op b x) :
    op (op a (op a x)) a = op (op b (op a x)) b :=
  FiniteMagmaE677.collision_cancel op h x a b hcol
