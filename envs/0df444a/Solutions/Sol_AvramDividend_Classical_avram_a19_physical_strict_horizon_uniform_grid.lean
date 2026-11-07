-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_physical_strict_horizon_uniform_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T08:37:43.667283+00:00
-- url     : https://prove2.me/submissions/911ec210-4f9e-4fdb-89f9-a2edb4024dde

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical Filter
open scoped NNReal
noncomputable section

/-- Increasing physical cells with the final endpoint strictly before the horizon. -/
theorem solution (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n, u n 0 = 0 ∧ ((u n (n + 1) : ℝ) = T - δ n)) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) := by
  let u : ℕ → ℕ → ℝ≥0 := fun n i =>
    ⟨T * (i : ℝ) / ((n : ℝ) + 2),
      div_nonneg (mul_nonneg (le_of_lt hT) (Nat.cast_nonneg i))
        (by positivity)⟩
  refine ⟨u, ?_, ?_, ?_⟩
  · intro n
    constructor
    · apply Subtype.ext
      simp [u]
    · change T * (((n + 1 : ℕ) : ℝ)) / ((n : ℝ) + 2) =
        T - T / ((n : ℝ) + 2)
      have hn : (n : ℝ) + 2 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
  · intro n i hi
    change T * (i : ℝ) / ((n : ℝ) + 2) ≤
      T * (((i + 1 : ℕ) : ℝ)) / ((n : ℝ) + 2)
    apply div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ i) (le_of_lt hT))
      (by positivity)
  · intro n i
    rfl
