-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB118_original_uniform_physical_grid_monotone_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:32:53.084182+00:00
-- url     : https://prove2.me/submissions/018cfa03-557c-4589-8664-f7dca0f37c12

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
noncomputable section
/-- The original uniform physical Gaussian grid satisfies the required step law. -/
theorem solution (n m : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    Monotone s ∧ s 0 = 0 ∧
      ∀ i : ℕ, s (i + 1) = s i + Δ := by
  dsimp
  constructor
  · intro i j hij
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)
  constructor
  · simp
  · intro i
    push_cast
    ring
