-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_actual_canonical_grid_monotone_zero_and_reaches_stop_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:08:27.694553+00:00
-- url     : https://prove2.me/submissions/6698ba5b-3991-49fe-a80d-88837263e228

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (n j : ℕ) (t : ℝ≥0) (ht : t ≤ (n : ℝ≥0)) :
    let u : ℕ → ℝ≥0 :=
      fun i => min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    let m : ℕ := (n + 1) * (j + 1)
    Monotone u ∧ u 0 = 0 ∧ u m = t := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro i k hik
    have hdiv :
        (i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0) ≤
        (k : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0) := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hik) (by positivity)
    exact min_le_min_right t hdiv
  · simp
  · have hj : ((j + 1 : ℕ) : ℝ≥0) ≠ 0 := by positivity
    have hcancel :
        (((n + 1) * (j + 1) : ℕ) : ℝ≥0) /
          ((j + 1 : ℕ) : ℝ≥0) = ((n + 1 : ℕ) : ℝ≥0) := by
      rw [Nat.cast_mul]
      field_simp [hj]
    have hle : t ≤ ((n + 1 : ℕ) : ℝ≥0) := by
      exact le_trans ht (by exact_mod_cast Nat.le_succ n)
    rw [hcancel, min_eq_right hle]
