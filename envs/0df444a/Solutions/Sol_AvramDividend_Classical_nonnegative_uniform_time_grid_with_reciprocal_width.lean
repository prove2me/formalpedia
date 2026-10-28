-- Prove2me | solution 1 for AvramDividend.Classical.nonnegative_uniform_time_grid_with_reciprocal_width
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:18:59.689105+00:00
-- url     : https://prove2.me/submissions/4a03dd9a-d66a-4498-945f-a600cb3dafeb

import Mathlib
open scoped NNReal
theorem solution
    (T : ℝ≥0) (N : ℕ) (hN : 0 < N) :
    ∃ (ts : ℕ → ℝ≥0) (δ : ℝ≥0),
      ts 0 = 0 ∧ ts N = T ∧
      (∀ k : ℕ, k < N → ts k ≤ ts (k + 1)) ∧
      (∀ k : ℕ, k < N → ts (k + 1) ≤ T) ∧
      (∀ k : ℕ, k < N → ts (k + 1) - ts k = δ) ∧
      δ = T / (N : ℝ≥0) := by
  have hN' : (N : ℝ≥0) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨fun k => (k : ℝ≥0) * (T / N), T / N, by simp, ?_, ?_, ?_, ?_, rfl⟩
  · show (N : ℝ≥0) * (T / N) = T
    rw [mul_div_cancel₀ _ hN']
  · intro k _
    show (k : ℝ≥0) * (T / N) ≤ ((k + 1 : ℕ) : ℝ≥0) * (T / N)
    gcongr
    exact_mod_cast Nat.le_succ k
  · intro k hk
    show ((k + 1 : ℕ) : ℝ≥0) * (T / N) ≤ T
    calc ((k + 1 : ℕ) : ℝ≥0) * (T / N) ≤ (N : ℝ≥0) * (T / N) := by
          gcongr; exact_mod_cast hk
      _ = T := mul_div_cancel₀ _ hN'
  · intro k _
    show ((k + 1 : ℕ) : ℝ≥0) * (T / N) - (k : ℝ≥0) * (T / N) = T / N
    rw [Nat.cast_succ, add_mul, one_mul, add_tsub_cancel_left]
