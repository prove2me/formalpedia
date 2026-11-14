-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB313_exact_original_gaussian_single_cell_prefactor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:13:40.324214+00:00
-- url     : https://prove2.me/submissions/5542fcf2-9f65-49a8-b6b8-ad22b350bc41

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal
noncomputable section

/-- Cubic dividend threshold and fourth-power Gaussian cell width yield exact fifth-order mass. -/
theorem solution (sigma : ℝ) (hsigma : 0 < sigma)
    (m : ℕ) (hm : 0 < m) :
    ENNReal.ofReal (1 / (sigma * Real.sqrt (2 * Real.pi))) *
      ENNReal.ofReal (1 / ((m : ℝ) ^ 3)) *
      ENNReal.ofReal (2 * Real.sqrt (1 / ((m : ℝ) ^ 4))) =
      (Real.toNNReal (2 /
        (sigma * Real.sqrt (2 * Real.pi) * ((m : ℝ) ^ 5))) : ℝ≥0∞) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpos : 0 < sigma * Real.sqrt (2 * Real.pi) := by positivity
  have hsq : (1 / ((m : ℝ) ^ 4)) =
      (1 / ((m : ℝ) ^ 2)) ^ 2 := by
    field_simp
  have hsqrt : Real.sqrt (1 / ((m : ℝ) ^ 4)) =
      1 / ((m : ℝ) ^ 2) := by
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hreal :
      (1 / (sigma * Real.sqrt (2 * Real.pi))) *
        (1 / ((m : ℝ) ^ 3)) *
        (2 * Real.sqrt (1 / ((m : ℝ) ^ 4))) =
      2 / (sigma * Real.sqrt (2 * Real.pi) * ((m : ℝ) ^ 5)) := by
    rw [hsqrt]
    field_simp
  have ha : 0 ≤ 1 / (sigma * Real.sqrt (2 * Real.pi)) := by positivity
  have hb : 0 ≤ 1 / ((m : ℝ) ^ 3) := by positivity
  have hc : 0 ≤ 2 * Real.sqrt (1 / ((m : ℝ) ^ 4)) := by positivity
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul
    (mul_nonneg ha hb)]
  rw [hreal]
  rfl
