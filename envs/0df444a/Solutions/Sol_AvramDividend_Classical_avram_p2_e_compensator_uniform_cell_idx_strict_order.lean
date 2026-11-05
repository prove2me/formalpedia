-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_uniform_cell_idx_strict_order
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:40:08.371617+00:00
-- url     : https://prove2.me/submissions/6c81c0f8-555a-461b-8893-4e68fb845ca8

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal

/-- Injective half-open uniform cell indices preserve the physical time order. -/
theorem solution
    (F : Finset ℝ≥0) (δ : ℝ≥0) (idx : ℝ≥0 → ℕ)
    (hcell : ∀ u ∈ F,
      (idx u : ℝ≥0) * δ < u ∧
      u ≤ (((idx u + 1 : ℕ) : ℝ≥0) * δ))
    (hinj : Set.InjOn idx (F : Set ℝ≥0)) :
    ∀ u ∈ F, ∀ v ∈ F, u < v → idx u < idx v := by
  intro u hu v hv huv
  have hne : idx u ≠ idx v := by
    intro heq
    have huvEq : u = v := hinj hu hv heq
    exact (ne_of_lt huv) huvEq
  by_contra hnot
  have hle : idx v ≤ idx u := Nat.le_of_not_gt hnot
  have hlt : idx v < idx u := lt_of_le_of_ne hle (Ne.symm hne)
  have hsucc : idx v + 1 ≤ idx u := Nat.succ_le_of_lt hlt
  have hcast : ((idx v + 1 : ℕ) : ℝ≥0) ≤ (idx u : ℝ≥0) := by
    exact_mod_cast hsucc
  have hmul : (((idx v + 1 : ℕ) : ℝ≥0) * δ) ≤
      (idx u : ℝ≥0) * δ := mul_le_mul_of_nonneg_right hcast (by positivity)
  have hvu : v < u :=
    lt_of_le_of_lt (le_trans (hcell v hv).2 hmul) (hcell u hu).1
  exact (lt_asymm huv hvu)
