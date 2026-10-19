-- Prove2me | solution 1 for FiniteMagmaE677.e677_implies_e255_finite_of_two_left_orbit_complement_escape
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-17T05:10:43.94367+00:00
-- url     : https://prove2.me/submissions/baaef84f-e89b-4b7c-becc-d7e9dfc7159e

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_FiniteMagmaE677
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.VecNotation

/-!
# Product transport: the two-outsider escape statement gives E255

Platform port of `e677_fixer_exists_of_d7_leaf` and
`e677_implies_e255_of_d7_leaf` (Adam McKenna, The Missing Pair, private
repository, `lean/E677/Transport.lean`), restated over an explicit operation
with the `FiniteMagmaE677` definitions.

`K` is the order-7 E677 magma of database model 242. The left orbit of `0` in
`K` is `0, 6, 1, 3, 4, 2`, so `5` is the only element outside it, and
`L_0^2(0) = 1` with `1 ◇ 0 = 5`. In `α × K` the point `(x, 0)` therefore
satisfies every hypothesis of the two-outsider escape statement as soon as
`x ◇ x ≠ x`, and a fixer of `(x, 0)` projects to a fixer of `x`.
-/

universe u

namespace FiniteMagmaE677.ProductTransport

/-- Table of `K` (database model 242); `ktab a b = a ◇ b`, row = left operand. -/
def ktab : Fin 7 → Fin 7 → Fin 7 :=
  ![![6, 3, 0, 4, 2, 5, 1],
    ![5, 6, 2, 0, 1, 4, 3],
    ![2, 0, 6, 3, 5, 1, 4],
    ![1, 2, 5, 6, 4, 3, 0],
    ![0, 4, 3, 1, 6, 2, 5],
    ![3, 1, 4, 5, 0, 6, 2],
    ![4, 5, 1, 2, 3, 0, 6]]

/-- `K` satisfies E677 (all 49 instances checked by `decide`). -/
theorem ktab_e677 : FiniteMagmaE677.E677 ktab := by
  unfold FiniteMagmaE677.E677
  decide

theorem ktab_step_ne_five : ∀ z : Fin 7, z ≠ 5 → ktab 0 z ≠ 5 := by decide

/-- `5` is not on the left orbit of `0` in `K`. -/
theorem ktab_orbit_ne_five (n : ℕ) : (ktab 0)^[n] 0 ≠ 5 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ktab_step_ne_five _ ih

/-- Right translation by `0` sends the orbit point `L_0^2(0) = 1` to `5`. -/
theorem ktab_escape : ktab ((ktab 0)^[2] 0) 0 = 5 := by decide

/-- Componentwise operation on `α × K`. -/
def prodOp {α : Type u} (op : α → α → α) : α × Fin 7 → α × Fin 7 → α × Fin 7 :=
  fun p q => (op p.1 q.1, ktab p.2 q.2)

theorem prodOp_e677 {α : Type u} (op : α → α → α) (h : FiniteMagmaE677.E677 op) :
    FiniteMagmaE677.E677 (prodOp op) := by
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
  exact Prod.ext (h x₁ y₁) (ktab_e677 x₂ y₂)

/-- The second coordinate of a left orbit in `α × K` is the left orbit in `K`. -/
theorem prodOp_orbit_snd {α : Type u} (op : α → α → α) (X : α × Fin 7) (n : ℕ) :
    ((prodOp op X)^[n] X).2 = (ktab X.2)^[n] X.2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change ktab X.2 ((prodOp op X)^[n] X).2 = ktab X.2 ((ktab X.2)^[n] X.2)
      rw [ih]

/-- A point with second coordinate `5` is outside the left orbit of `(x, 0)`. -/
theorem not_inLeftOrbit_of_snd_eq_five {α : Type u} (op : α → α → α) (x : α)
    (p : α × Fin 7) (hp : p.2 = 5) :
    ¬ FiniteMagmaE677.InLeftOrbit (prodOp op) (x, 0) p := by
  rintro ⟨i, hi⟩
  apply ktab_orbit_ne_five i
  have h2 : p.2 = (ktab 0)^[i] 0 :=
    (congrArg Prod.snd hi).trans (prodOp_orbit_snd op (x, 0) i)
  exact h2.symm.trans hp

/-- Lemma 13.1(ii): in a finite E677 magma every fixer of `x` is `(x ◇ x) ◇ x`. -/
theorem fixer_eq {α : Type u} [Fintype α] (op : α → α → α)
    (h : FiniteMagmaE677.E677 op) (x y : α) (hfix : op y x = x) :
    y = op (op x x) x := by
  have hinj (z : α) : Function.Injective (op z) := by
    apply Finite.injective_iff_surjective.mpr
    intro a
    exact ⟨op a (op (op z a) z), (h a z).symm⟩
  have inv_at_x : op y (op x (op x y)) = x := by
    have hi := (h x y).symm
    rwa [hfix] at hi
  have hx_xy := hinj y (hfix.trans inv_at_x.symm)
  exact hinj x (hinj x (hx_xy.symm.trans (h x x)))

end FiniteMagmaE677.ProductTransport

open FiniteMagmaE677.ProductTransport in
/--
If the two-outsider escape statement (Sub-goal 3) holds for every finite E677
magma, then every finite E677 magma satisfies E255.
-/
theorem solution
    (hSG3 : ∀ {β : Type u} [Fintype β] (op : β → β → β), FiniteMagmaE677.E677 op →
      ∀ x : β, op x x ≠ x →
        (∃ a b : β, a ≠ b ∧
          ¬ FiniteMagmaE677.InLeftOrbit op x a ∧ ¬ FiniteMagmaE677.InLeftOrbit op x b) →
        (∃ a : β, FiniteMagmaE677.InLeftOrbit op x a ∧
          ¬ FiniteMagmaE677.InLeftOrbit op x (op a x)) →
        FiniteMagmaE677.HasFixerAt op x)
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op) :
    FiniteMagmaE677.E255 op := by
  intro x
  -- First a fixer of `x`.
  have hfixer : ∃ y : α, op y x = x := by
    by_cases hid : op x x = x
    · exact ⟨x, hid⟩
    · have hni : prodOp op (x, 0) (x, 0) ≠ (x, 0) := fun hEq =>
        hid (congrArg Prod.fst hEq)
      have htwo : ∃ a b : α × Fin 7, a ≠ b ∧
          ¬ FiniteMagmaE677.InLeftOrbit (prodOp op) (x, 0) a ∧
            ¬ FiniteMagmaE677.InLeftOrbit (prodOp op) (x, 0) b :=
        ⟨(x, 5), (op x x, 5), fun hEq => hid (congrArg Prod.fst hEq).symm,
          not_inLeftOrbit_of_snd_eq_five op x _ rfl,
          not_inLeftOrbit_of_snd_eq_five op x _ rfl⟩
      have hescape : ∃ a : α × Fin 7, FiniteMagmaE677.InLeftOrbit (prodOp op) (x, 0) a ∧
          ¬ FiniteMagmaE677.InLeftOrbit (prodOp op) (x, 0) (prodOp op a (x, 0)) := by
        refine ⟨(prodOp op (x, 0))^[2] (x, 0), ⟨2, rfl⟩, ?_⟩
        apply not_inLeftOrbit_of_snd_eq_five op x
        change ktab ((prodOp op (x, 0))^[2] (x, 0)).2 0 = 5
        rw [prodOp_orbit_snd op (x, 0) 2]
        exact ktab_escape
      obtain ⟨⟨y₁, _y₂⟩, hy⟩ :=
        hSG3 (prodOp op) (prodOp_e677 op h) (x, 0) hni htwo hescape
      exact ⟨y₁, congrArg Prod.fst hy⟩
  -- Then E255 at `x` from fixer uniqueness.
  obtain ⟨y, hy⟩ := hfixer
  have hy' : y = op (op x x) x := fixer_eq op h x y hy
  rw [← hy']
  exact hy.symm

#print axioms solution
