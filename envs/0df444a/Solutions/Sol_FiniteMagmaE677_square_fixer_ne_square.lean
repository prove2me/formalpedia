-- Prove2me | solution 1 for FiniteMagmaE677.square_fixer_ne_square
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T10:05:10.216732+00:00
-- url     : https://prove2.me/submissions/2f620f02-67eb-4bf1-8f1e-ffb6a5feca2b

import Definitions.Def_FiniteMagmaE677
import Theorems.Thm_FiniteMagmaE677_left_bijective
import Theorems.Thm_FiniteMagmaE677_backward_recurrence
import Theorems.Thm_FiniteMagmaE677_no_left_period_three

/-!
# An element and its square cannot fix each other

Suppose `s ⋄ b = b` (s is a fixer of b) and `b ⋄ b = s` (the square of b is
that fixer). Writing `ω = b ⋄ s`, the backward recurrence at `(b, s)` gives
`b = b ⋄ ω`, since `s ⋄ b = b` turns it into
`b = (s ⋄ b) ⋄ ((s ⋄ (s ⋄ b)) ⋄ s) = b ⋄ (b ⋄ s)`.

The left translation `L_b` then cycles
`b ↦ s ↦ ω ↦ b`, i.e. `L_b³ b = b`, so `b ⋄ b = b` by
`no_left_period_three` (and then `s = b ⋄ b = b`).

Consequently, in a finite E677 magma with a fixer `s ⋄ b = b` and `s ≠ b`,
the square `b ⋄ b` differs from the fixer `s`: the fixer of a non-idempotent
element is never its own square.
-/

universe u

theorem FiniteMagmaE677.square_fixer_ne_square {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (s b : α)
    (hs : op s b = b) (hsq : op b b = s) : op b b = b := by
  -- backward recurrence at (b, s), rewritten with s ⋄ b = b
  have hbr := FiniteMagmaE677.backward_recurrence op h b s
  rw [hs, hs] at hbr
  -- hbr : b = op b (op b s)   (i.e. b = b ⋄ ω with ω = b ⋄ s)
  have homega : op b (op b s) = b := hbr.symm
  -- L_b cycles b ↦ s ↦ (b ⋄ s) ↦ b
  have hper : op b (op b (op b b)) = b := by
    rw [hsq]
    exact homega
  exact FiniteMagmaE677.no_left_period_three op h b hper

theorem solution {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (s b : α)
    (hs : op s b = b) (hsq : op b b = s) : op b b = b :=
  FiniteMagmaE677.square_fixer_ne_square op h s b hs hsq
