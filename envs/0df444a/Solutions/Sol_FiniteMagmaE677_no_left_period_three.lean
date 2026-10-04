-- Prove2me | solution 1 for FiniteMagmaE677.no_left_period_three
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T07:43:41.056045+00:00
-- url     : https://prove2.me/submissions/2a3b73df-8e79-459b-815d-42257b3f3ddb

import Definitions.Def_FiniteMagmaE677
import Theorems.Thm_FiniteMagmaE677_left_bijective
import Theorems.Thm_FiniteMagmaE677_backward_recurrence
import Theorems.Thm_FiniteMagmaE677_fixer_unique
import Theorems.Thm_FiniteMagmaE677_collision_cancel

/-!
# No element of a finite E677 magma has left-orbit period exactly three

Write `L_x z = x ⋄ z`, `z₁ = x ⋄ x`, `z₂ = x ⋄ z₁`, and suppose
`x ⋄ z₂ = x`. We show `x ⋄ x = x`, so the `L_x`-orbit of `x` cannot have
exact period three (combined with `no_left_period_two`, every orbit of a
finite E677 magma has length one or at least four).

The chain of identities, each obtained from E677, the backward recurrence,
the collision cancellation identity, or fixer uniqueness, together with left
cancellation:

1. `c₁ = z₁`, i.e. `z₁ ⋄ x = z₁`      (E677 at `(x,x)` twice cancelled)
2. `z₂ ⋄ z₁ = z₁`                      (E677 at `(z₂,x)` cancelled)
3. `z₂ = (z₁ ⋄ z₁) ⋄ z₁`               (fixer uniqueness at `z₁`)
4. `x = z₁ ⋄ z₂`                       (backward recurrence at `(x,z₁)`)
5. `z₁ ⋄ z₁ = z₁`                      (E677 at `(x,z₁)` cancelled twice)
6. `z₂ ⋄ x = z₁`                       (collision identity for `x`, `z₁`)
7. `z₁ ⋄ z₁ = x`                       (E677 at `(z₁,x)` cancelled)
Steps 5 and 7 give `x = z₁ = x ⋄ x`, the claim.
-/

universe u

theorem FiniteMagmaE677.no_left_period_three {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x : α)
    (hper : op x (op x (op x x)) = x) : op x x = x := by
  by_contra hni
  have hinj := (FiniteMagmaE677.left_bijective op h x).1
  have hinj1 := (FiniteMagmaE677.left_bijective op h (op x x)).1
  -- Step 1: (x ⋄ x) ⋄ x = x ⋄ x
  have h1 : op (op x x) x = op x x := by
    apply hinj
    apply hinj
    calc op x (op x (op (op x x) x)) = x := (h x x).symm
      _ = op x (op x (op x x)) := hper.symm
  -- Step 2: (x ⋄ (x ⋄ x)) ⋄ (x ⋄ x) = x ⋄ x
  have h2 : op (op x (op x x)) (op x x) = op x x := by
    have hE2 := h (op x (op x x)) x
    rw [hper] at hE2
    exact hinj hE2.symm
  -- Step 3: fixer uniqueness at z₁ with witness z₂
  have h3 := FiniteMagmaE677.fixer_unique op h (op x x) (op x (op x x)) h2
  -- Step 4: x = z₁ ⋄ z₂
  have h4 : x = op (op x x) (op x (op x x)) := by
    have hbr := FiniteMagmaE677.backward_recurrence op h x (op x x)
    rw [h1, ← h3] at hbr
    exact hbr
  -- Step 5: (z₁ ⋄ z₁) = z₁
  have h5 : op (op x x) (op x x) = op x x := by
    have hE3 := h x (op x x)
    rw [h1] at hE3
    exact hinj (hinj1 (hE3.symm.trans h4))
  -- Step 6: z₂ ⋄ x = z₁  (collision of x and z₁ under right translation)
  have h6 : op (op x (op x x)) x = op x x := by
    have hcc := FiniteMagmaE677.collision_cancel op h x x (op x x) h1.symm
    rw [h5, h5] at hcc
    exact hcc
  -- Step 7: z₁ ⋄ z₁ = x, contradicting Step 5
  have h7 : op (op x x) (op x x) = x := by
    have hE4 := h (op x x) x
    rw [h6] at hE4
    exact hinj hE4.symm
  exact hni (h5.symm.trans h7)

theorem solution {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x : α)
    (hper : op x (op x (op x x)) = x) : op x x = x :=
  FiniteMagmaE677.no_left_period_three op h x hper
