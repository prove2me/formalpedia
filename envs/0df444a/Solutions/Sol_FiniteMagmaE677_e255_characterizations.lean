-- Prove2me | solution 1 for FiniteMagmaE677.e255_characterizations
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T16:15:56.286536+00:00
-- url     : https://prove2.me/submissions/3cd4a1e0-f3cf-47bd-a7eb-897e07e6f82e

import Definitions.Def_FiniteMagmaE677
import Theorems.Thm_FiniteMagmaE677_left_bijective
import Theorems.Thm_FiniteMagmaE677_fixer_unique

/-!
# Equivalent characterizations of equation 255 at an element

Let `x` be an element of a finite magma satisfying E677 and write
`S y = y ⋄ y`. The following are equivalent:

(i)   `x = ((x ⋄ x) ⋄ x) ⋄ x`                     (equation 255 at x)
(iii) `∃ y, y ⋄ x = x`                            (x has a fixer)
(iv)  `∃ w, (x ⋄ w) ⋄ x = x`
(v)   `∃ z, x ⋄ (z ⋄ x) = z`
(vi)  `∃ y, (x ⋄ y) ⋄ x = y`
(vii) `∃ y, x ⋄ (y ⋄ y) = y`

The uniqueness of the fixer (`y ⋄ x = x → y = (x ⋄ x) ⋄ x`) is fixer
uniqueness, Lemma 13.1(ii). This is the finite-magma form of the blueprint's
Lemma on equivalent characterizations of 255 (Chapter 13).

Proof of the implications:
* (i) ↔ (iii): the witness of (i) is a fixer; conversely a fixer equals
  `(x ⋄ x) ⋄ x` by uniqueness.
* (iii) ↔ (iv): left translation by `x` is surjective, so the fixer `y` has
  the form `x ⋄ w`; and `x ⋄ w` with `(x ⋄ w) ⋄ x = x` is a fixer.
* (iv) → (v): E677 at `(w, x)` reads `w = x ⋄ (w ⋄ ((x ⋄ w) ⋄ x))`; with
  `(x ⋄ w) ⋄ x = x` this is the (v)-identity for `z := w`.
* (v) → (iv): E677 at `(z, x)` reads `z = x ⋄ (z ⋄ ((x ⋄ z) ⋄ x))`; cancelling
  `x ⋄ (z ⋄ ·)` against the (v)-identity gives `(x ⋄ z) ⋄ x = x`.
* (v) ↔ (vi): the maps `z ↦ x ⋄ z` and `y ↦ y ⋄ x` transport solutions.
* (vi) ↔ (vii): E677 at `(y, x)` reads `y = x ⋄ (y ⋄ ((x ⋄ y) ⋄ x))`; with
  `(x ⋄ y) ⋄ x = y` this is `x ⋄ (y ⋄ y) = y`, and conversely cancelling
  `y ⋄ ·` recovers `(x ⋄ y) ⋄ x = y` from it.
-/

universe u

theorem FiniteMagmaE677.e255_characterizations {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x : α) :
    (x = op (op (op x x) x) x ↔ ∃ y : α, op y x = x) ∧
    ((∃ y : α, op y x = x) ↔ ∃ w : α, op (op x w) x = x) ∧
    ((∃ w : α, op (op x w) x = x) ↔ ∃ z : α, op x (op z x) = z) ∧
    ((∃ z : α, op x (op z x) = z) ↔ ∃ y : α, op (op x y) x = y) ∧
    ((∃ y : α, op (op x y) x = y) ↔ ∃ y : α, op x (op y y) = y) := by
  have hinjx := (FiniteMagmaE677.left_bijective op h x).1
  have hsurjx := (FiniteMagmaE677.left_bijective op h x).2
  -- (i) ↔ (iii)
  have iff1 : x = op (op (op x x) x) x ↔ ∃ y : α, op y x = x := by
    constructor
    · intro hx; exact ⟨op (op x x) x, hx.symm⟩
    · rintro ⟨y, hy⟩
      have hfix := FiniteMagmaE677.fixer_unique op h x y hy
      rw [← hfix]
      exact hy.symm
  -- (iii) ↔ (iv)
  have iff2 : (∃ y : α, op y x = x) ↔ (∃ w : α, op (op x w) x = x) := by
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨w, hw⟩ := hsurjx y
      exact ⟨w, by rw [hw]; exact hy⟩
    · rintro ⟨w, hw⟩; exact ⟨op x w, hw⟩
  -- (iv) ↔ (v)
  have iff3 : (∃ w : α, op (op x w) x = x) ↔ (∃ z : α, op x (op z x) = z) := by
    constructor
    · rintro ⟨w, hw⟩
      have hE := h w x
      -- w = op x (op w (op (op x w) x))
      rw [hw] at hE
      exact ⟨w, hE.symm⟩
    · rintro ⟨z, hz⟩
      have hE := h z x
      -- z = op x (op z (op (op x z) x))
      have key : op x (op z (op (op x z) x)) = op x (op z x) :=
        hE.symm.trans hz.symm
      have key2 := hinjx key
      -- op z (op (op x z) x) = op z x
      exact ⟨z, ((FiniteMagmaE677.left_bijective op h z).1) key2⟩
  -- (v) ↔ (vi)
  have iff4 : (∃ z : α, op x (op z x) = z) ↔ (∃ y : α, op (op x y) x = y) := by
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨op z x, ?_⟩
      rw [hz]
    · rintro ⟨y, hy⟩
      refine ⟨op x y, ?_⟩
      rw [hy]
  -- (vi) ↔ (vii)
  have iff5 : (∃ y : α, op (op x y) x = y) ↔ (∃ y : α, op x (op y y) = y) := by
    constructor
    · rintro ⟨y, hy⟩
      have hE := h y x
      -- y = op x (op y (op (op x y) x))
      rw [hy] at hE
      exact ⟨y, hE.symm⟩
    · rintro ⟨y, hy⟩
      have hE := h y x
      -- y = op x (op y (op (op x y) x))
      have key : op x (op y (op (op x y) x)) = op x (op y y) :=
        hE.symm.trans hy.symm
      have key2 := hinjx key
      exact ⟨y, ((FiniteMagmaE677.left_bijective op h y).1) key2⟩
  exact ⟨iff1, iff2, iff3, iff4, iff5⟩

theorem solution {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x : α) :
    (x = op (op (op x x) x) x ↔ ∃ y : α, op y x = x) ∧
    ((∃ y : α, op y x = x) ↔ ∃ w : α, op (op x w) x = x) ∧
    ((∃ w : α, op (op x w) x = x) ↔ ∃ z : α, op x (op z x) = z) ∧
    ((∃ z : α, op x (op z x) = z) ↔ ∃ y : α, op (op x y) x = y) ∧
    ((∃ y : α, op (op x y) x = y) ↔ ∃ y : α, op x (op y y) = y) :=
  FiniteMagmaE677.e255_characterizations op h x
