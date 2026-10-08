-- Prove2me | solution 2 for FiniteMagmaE677.collision_cancel
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T02:16:07.337761+00:00
-- url     : https://prove2.me/submissions/e3a9ea35-6586-444c-b8eb-fc95b5657236

import Definitions.Def_FiniteMagmaE677
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

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

private theorem collision_cancel_left_bijective {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (y : α) :
    Function.Bijective (op y) := by
  apply Finite.surjective_iff_bijective.mp
  intro x
  exact ⟨op x (op (op y x) y), (h x y).symm⟩

private theorem collision_cancel_backward_recurrence {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x y : α) :
    x = op (op y x) (op (op y (op y x)) y) := by
  exact (collision_cancel_left_bijective op h y).1 (h (op y x) y)

theorem FiniteMagmaE677.collision_cancel {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x a b : α)
    (hcol : op a x = op b x) :
    op (op a (op a x)) a = op (op b (op a x)) b := by
  have hbr1 := collision_cancel_backward_recurrence op h x a
  have hbr2 := collision_cancel_backward_recurrence op h x b
  have hinj := (collision_cancel_left_bijective op h (op a x)).1
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
