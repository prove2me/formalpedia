-- Prove2me | solution 1 for FiniteMagmaE677.linear_collision_injective
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T12:16:27.618552+00:00
-- url     : https://prove2.me/submissions/743c3993-d29f-4502-b68e-dd1a9d35b2ce

import Definitions.Def_FiniteMagmaE677
import Theorems.Thm_FiniteMagmaE677_left_bijective

/-!
# Right-translation injectivity from weak linearity

In a finite magma satisfying E677, suppose that right-translation collisions
always propagate to full left-translation agreement: whenever `y ⋄ x = y' ⋄ x`,
also `y ⋄ z = y' ⋄ z` for every `z`. Then right translation by `x` is
injective.

The proof is the magma-level core of the blueprint's "no linear
counterexamples" argument (Equational Theories Project, Chapter 13, Lemma on
linear models). Writing `p = y ⋄ x = y' ⋄ x`, E677 at `(x, y)` and `(x, y')`
gives

  `x = L_y (L_x (L_p y))` and `x = L_{y'} (L_x (L_p y'))`.

Since `L_{y'} = L_y` by the hypothesis, cancelling the three injective left
translations yields `y = y'`.
-/

universe u

theorem FiniteMagmaE677.linear_collision_injective {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x : α)
    (hlin : ∀ y y' z : α, op y x = op y' x → op y z = op y' z) :
    ∀ y y' : α, op y x = op y' x → y = y' := by
  intro y y' hcol
  have hinjy := (FiniteMagmaE677.left_bijective op h y).1
  have hinjx := (FiniteMagmaE677.left_bijective op h x).1
  have hinjp := (FiniteMagmaE677.left_bijective op h (op y x)).1
  have E1 := h x y
  have E2 := h x y'
  rw [← hcol] at E2
  -- E1 : x = op y (op x (op (op y x) y))
  -- E2 : x = op y' (op x (op (op y x) y'))
  -- rewrite the outer op y' to op y using hlin
  have E2' : x = op y (op x (op (op y x) y')) := by
    rw [hlin y y' (op x (op (op y x) y')) hcol]
    exact E2
  -- cancel L_y
  have key : op x (op (op y x) y) = op x (op (op y x) y') :=
    hinjy (E1.symm.trans E2')
  -- cancel L_x
  have key2 : op (op y x) y = op (op y x) y' := hinjx key
  -- cancel L_{op y x}
  exact hinjp key2

theorem solution {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x : α)
    (hlin : ∀ y y' z : α, op y x = op y' x → op y z = op y' z) :
    ∀ y y' : α, op y x = op y' x → y = y' :=
  FiniteMagmaE677.linear_collision_injective op h x hlin
