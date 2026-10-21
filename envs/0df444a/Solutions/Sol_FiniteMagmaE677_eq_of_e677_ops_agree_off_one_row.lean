-- Prove2me | solution 1 for FiniteMagmaE677.eq_of_e677_ops_agree_off_one_row
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-20T22:47:30.248092+00:00
-- url     : https://prove2.me/submissions/dadc4240-e857-4958-89c7-ddc0c79ce075

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_FiniteMagmaE677
import Mathlib

/-!
# One-row rigidity for two `E677` tables

Let `op` (old) and `op'` (new) be two operations on the same finite carrier, both satisfying
`E677`. If `op' u v = op u v` for every `u ≠ a` and every `v`, then `op' = op`.

Proof. Every row of a finite `E677` table is a bijection. Let `D` be the set of columns `y` with
`op' a y ≠ op a y`, and let `f = op (op a a) a`.
1. Support rule: if rows `b`, `t` are the same in both tables and `op b t = a`, then
   `op' a b = op a b`. Hence for `y ∈ D` with `y ≠ a`, the old preimage of `a` under row `y` is
   `a`, so `op y a = a`, and fixer uniqueness gives `y = f`. So `D ⊆ {a, f}`.
2. An injective map and a surjective map that agree off one point agree everywhere. So if
   `D ⊆ {a}`, then `D = ∅`.
3. Otherwise `f ≠ a`, `f ∈ D` and `op f a = a`. Then `op' a f = op a a`, and old `E677` at
   `(a, f)` gives `op a (op a f) = a`, so `op a f ∉ {a, f}` and `op' a (op a f) = a`.
4. New `E677` at `(a, f)` gives `op' a (op a a) = a`. Cancelling the new row `a`, then the old
   row `a`, gives `a = f`, which is false.
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

/-- Left multiplication by `y` is injective in a finite `E677` table. -/
private theorem leftMul_inj [Finite α] {op : α → α → α} (h : E677 op) (y : α) :
    Function.Injective (op y) :=
  Finite.injective_iff_surjective.mpr (leftMul_surj h y)

/-- Left cancellation in a finite `E677` table. -/
private theorem left_cancel [Finite α] {op : α → α → α} (h : E677 op) (y : α) {a b : α}
    (hab : op y a = op y b) : a = b :=
  leftMul_inj h y hab

/-- Fixer uniqueness in a finite `E677` table: if `op y x = x`, then `y = op (op x x) x`. -/
private theorem fixer_unique [Finite α] {op : α → α → α} (h : E677 op) {x y : α}
    (hfix : op y x = x) : y = op (op x x) x := by
  have hinv : op y (op x (op x y)) = x := by
    have h0 := (h x y).symm
    rwa [hfix] at h0
  have hxy : x = op x (op x y) := left_cancel h y (by rw [hfix, hinv])
  exact left_cancel h x (left_cancel h x (hxy.symm.trans (h x x)))

/-- An injective map and a surjective map that agree at every point other than `p` also agree
at `p`. -/
private theorem apply_eq_of_forall_ne {g₁ g₂ : α → α} (hg₁ : Function.Injective g₁)
    (hg₂ : Function.Surjective g₂) {p : α} (hoff : ∀ x, x ≠ p → g₁ x = g₂ x) : g₁ p = g₂ p := by
  obtain ⟨q, hq⟩ := hg₂ (g₁ p)
  by_cases hqp : q = p
  · subst hqp
    exact hq.symm
  · exact absurd (hg₁ ((hoff q hqp).trans hq)) hqp

/-- Support rule: if rows `b` and `t` are the same in both finite `E677` tables and
`op b t = a`, then `op' a b = op a b`. -/
private theorem op_eq_of_rows_agree [Finite α] {op op' : α → α → α} (h : E677 op)
    (h' : E677 op') {a b t : α} (hb : ∀ y, op' b y = op b y) (ht : ∀ y, op' t y = op t y)
    (hbt : op b t = a) : op' a b = op a b := by
  have hold : t = op b (op t (op a b)) := by
    have h0 := h t b
    rwa [hbt] at h0
  have hnew : t = op b (op t (op' a b)) := by
    have h0 := h' t b
    rwa [hb t, hbt, ht, hb] at h0
  exact left_cancel h t (left_cancel h b (hnew.symm.trans hold))

/-- One-row rigidity: two finite `E677` tables that agree off row `a` are equal. -/
private theorem eq_of_rows_agree_except [Finite α] {op op' : α → α → α} (hM : E677 op)
    (hN : E677 op') (a : α) (h : ∀ u, u ≠ a → ∀ v, op' u v = op u v) : op' = op := by
  -- A changed column `y ≠ a` of row `a` is a fixer of `a` in the old table.
  have hcol : ∀ y, y ≠ a → op' a y ≠ op a y → op y a = a := by
    intro y hya hy
    obtain ⟨x, hx⟩ : ∃ x, op y x = a := ⟨_, (hM a y).symm⟩
    by_cases hxa : x = a
    · rwa [hxa] at hx
    · exact absurd (op_eq_of_rows_agree hM hN (h y hya) (h x hxa) hx) hy
  obtain ⟨f, hf⟩ : ∃ f, op (op a a) a = f := ⟨_, rfl⟩
  -- The changed columns of row `a` lie in `{a, f}`.
  have hD : ∀ y, op' a y ≠ op a y → y = a ∨ y = f := by
    intro y hy
    by_cases hya : y = a
    · exact Or.inl hya
    · exact Or.inr ((fixer_unique hM (hcol y hya hy)).trans hf)
  have hrow : ∀ v, op' a v = op a v := by
    by_cases hfa : f ≠ a ∧ op' a f ≠ op a f
    · exfalso
      obtain ⟨hfa, hDf⟩ := hfa
      have hfix : op f a = a := hcol f hfa hDf
      have hoff : ∀ y, y ≠ a → y ≠ f → op' a y = op a y := by
        intro y h1 h2
        by_contra hy
        rcases hD y hy with h3 | h3
        · exact h1 h3
        · exact h2 h3
      -- The new row `a` sends `f` to `op a a`.
      have hb : op' a f = op a a := by
        obtain ⟨q, hq⟩ : ∃ q, op a q = op' a f := leftMul_surj hM a (op' a f)
        by_cases hqa : q = a
        · rw [← hq, hqa]
        · by_cases hqf : q = f
          · rw [hqf] at hq
            exact absurd hq.symm hDf
          · exact absurd (left_cancel hN a ((hoff q hqa hqf).trans hq)) hqf
      -- Old `E677` at `(a, f)`: `op a (op a f) = a`.
      have hc : op a (op a f) = a := by
        have h1 := hM a f
        rw [hfix] at h1
        exact left_cancel hM f (h1.symm.trans hfix.symm)
      have hca : op a f ≠ a := by
        intro hc'
        have haa : op a a = a := by
          rw [hc'] at hc
          exact hc
        exact hfa (left_cancel hM a (haa.trans hc'.symm)).symm
      have hcf : op a f ≠ f := by
        intro hc'
        rw [hc'] at hc
        exact hfa (hc'.symm.trans hc)
      have hNc : op' a (op a f) = a := (hoff _ hca hcf).trans hc
      -- New `E677` at `(a, f)`: `op' a (op a a) = a`.
      have hNfa : op' f a = a := (h f hfa a).trans hfix
      have h2 := hN a f
      rw [hNfa, hb] at h2
      have hNb : op' a (op a a) = a := left_cancel hN f (h2.symm.trans hNfa.symm)
      have hbc : op a a = op a f := left_cancel hN a (hNb.trans hNc.symm)
      exact hfa (left_cancel hM a hbc).symm
    · have hoff : ∀ y, y ≠ a → op' a y = op a y := by
        intro y hya
        by_contra hy
        rcases hD y hy with h3 | h3
        · exact hya h3
        · rw [h3] at hya hy
          exact hfa ⟨hya, hy⟩
      intro v
      by_cases hva : v = a
      · rw [hva]
        exact apply_eq_of_forall_ne (leftMul_inj hN a) (leftMul_surj hM a) hoff
      · exact hoff v hva
  funext u v
  by_cases hua : u = a
  · rw [hua]
    exact hrow v
  · exact h u hua v

end RowRigidityHelpers

theorem solution
{α : Type u} [Finite α] (op op' : α → α → α)
(h : FiniteMagmaE677.E677 op) (h' : FiniteMagmaE677.E677 op') (a : α)
(hrows : ∀ u : α, u ≠ a → ∀ v : α, op' u v = op u v) :
op' = op :=
  RowRigidityHelpers.eq_of_rows_agree_except h h' a hrows

#print axioms solution
