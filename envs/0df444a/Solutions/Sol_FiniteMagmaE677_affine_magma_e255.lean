-- Prove2me | solution 1 for FiniteMagmaE677.affine_magma_e255
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T13:06:20.697985+00:00
-- url     : https://prove2.me/submissions/c14c5d2a-71dc-465b-a7f5-194dff2ce93b

import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.LinearCombination
import Definitions.Def_FiniteMagmaE677
import Theorems.Thm_FiniteMagmaE677_left_bijective
import Theorems.Thm_FiniteMagmaE677_fixer_unique
import Theorems.Thm_FiniteMagmaE677_linear_collision_injective

/-!
# No affine counterexamples to E677 → E255

Let R be a finite commutative ring and consider the affine operation
`x ⋄ y = a·x + b·y + c`. If it satisfies E677, then it satisfies E255.

This is the finite-ring (scalar-coefficient) form of the blueprint's "no
linear counterexamples" lemma (Equational Theories Project, Chapter 13):
any finite counterexample to the implication E677 → E255 must be non-affine.

Right-translation collisions force left-translation agreement, since
`a·y + b·x + c = a·y' + b·x + c` gives `a·y = a·y'` and hence
`a·y + b·z + c = a·y' + b·z + c` for every `z`. By
`linear_collision_injective`, right translation by each `x` is injective,
therefore surjective by finiteness, so each `x` has a fixer; fixer
uniqueness then turns the fixer into the E255 witness `(x ⋄ x) ⋄ x`.
-/

universe u v

theorem FiniteMagmaE677.affine_magma_e255 {R : Type v} [CommRing R] [Fintype R]
    (a b c : R)
    (h : FiniteMagmaE677.E677 (fun x y : R => a * x + b * y + c)) :
    FiniteMagmaE677.E255 (fun x y : R => a * x + b * y + c) := by
  set op : R → R → R := fun x y => a * x + b * y + c with hop
  intro x
  -- right-translation collisions propagate to left-translation agreement
  have hlin : ∀ y y' z : R, op y x = op y' x → op y z = op y' z := by
    intro y y' z h0
    simp only [hop] at h0 ⊢
    have hay : a * y = a * y' := by linear_combination h0
    rw [hay]
  -- right translation by x is injective, hence surjective
  obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.mp
    (FiniteMagmaE677.linear_collision_injective op h x hlin) x
  -- the fixer is (x ⋄ x) ⋄ x by uniqueness
  have hfix := FiniteMagmaE677.fixer_unique op h x y hy
  show x = op (op (op x x) x) x
  rw [← hfix]
  exact hy.symm

theorem solution {R : Type v} [CommRing R] [Fintype R]
    (a b c : R)
    (h : FiniteMagmaE677.E677 (fun x y : R => a * x + b * y + c)) :
    FiniteMagmaE677.E255 (fun x y : R => a * x + b * y + c) :=
  FiniteMagmaE677.affine_magma_e255 a b c h
