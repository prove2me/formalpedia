-- Prove2me | solution 1 for AvramDividend.Classical.bv_choose_finite_mesh_horizon_indices_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T21:58:33.425671+00:00
-- url     : https://prove2.me/submissions/b36288df-1720-43dd-b17c-ac9f5e8328a1

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal

theorem solution
    (T : ℝ≥0) (mesh : ℕ → ℝ≥0)
    (hpos : ∀ n : ℕ, 0 < mesh n) :
    ∃ M : ℕ → ℕ, ∀ n : ℕ,
      T ≤ (M n : ℝ≥0) * mesh n := by
  classical
  have hExists (n : ℕ) :
      ∃ k : ℕ, T ≤ (k : ℝ≥0) * mesh n := by
    obtain ⟨k, hk⟩ := exists_nat_gt (T / mesh n)
    have hDiv : T / mesh n ≤ (k : ℝ≥0) := le_of_lt hk
    have hMul : T ≤ (k : ℝ≥0) * mesh n :=
      (div_le_iff₀ (hpos n)).mp hDiv
    exact ⟨k, hMul⟩
  exact ⟨fun n => Classical.choose (hExists n),
    fun n => Classical.choose_spec (hExists n)⟩
