-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict6_uniform_physical_grid_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:05:24.961263+00:00
-- url     : https://prove2.me/submissions/b409e7be-88ca-4e65-9eea-55d74185ca75

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set
open scoped NNReal
noncomputable section

/-- Construct the exact nonnegative uniform physical grids of the original BV witness. -/
theorem solution (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n, u n 0 = 0 ∧ ((u n (n + 1) : ℝ) = T - δ n)) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) := by
  dsimp
  let u : ℕ → ℕ → ℝ≥0 := fun n i =>
    ⟨T * (i : ℝ) / ((n : ℝ) + 2),
      div_nonneg (mul_nonneg (le_of_lt hT) (Nat.cast_nonneg i)) (by positivity)⟩
  refine ⟨u, ?_, ?_⟩
  · intro n
    constructor
    · apply Subtype.ext
      simp [u]
    · change T * ((n + 1 : ℕ) : ℝ) / ((n : ℝ) + 2) =
        T - T / ((n : ℝ) + 2)
      have hn : (n : ℝ) + 2 ≠ 0 := by positivity
      push_cast
      field_simp [hn] <;> ring
  · intro n i hi
    change T * (i : ℝ) / ((n : ℝ) + 2) ≤
      T * ((i + 1 : ℕ) : ℝ) / ((n : ℝ) + 2)
    have hstep : (i : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ i
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hstep (le_of_lt hT)) (by positivity)
