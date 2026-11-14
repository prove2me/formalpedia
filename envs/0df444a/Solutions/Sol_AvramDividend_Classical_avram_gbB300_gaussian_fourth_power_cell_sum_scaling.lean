-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB300_gaussian_fourth_power_cell_sum_scaling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:58:56.376692+00:00
-- url     : https://prove2.me/submissions/317313b1-968d-4ac2-91c9-943169e289b1

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal
noncomputable section

/-- The original fourth-power Gaussian fifth-order cell mass sums at inverse linear order. -/
theorem solution (sigma : ℝ) (hsigma : 0 < sigma)
    (n m : ℕ) (hm : 0 < m) :
    ((n * m ^ 4 : ℕ) : ℝ≥0∞) *
      (Real.toNNReal (2 /
        (sigma * Real.sqrt (2 * Real.pi) * ((m : ℝ) ^ 5))) : ℝ≥0∞) =
      (Real.toNNReal ((2 * (n : ℝ)) /
        (sigma * Real.sqrt (2 * Real.pi))) : ℝ≥0∞) *
        (m : ℝ≥0∞)⁻¹ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : (0 : ℝ) < sigma * Real.sqrt (2 * Real.pi) := by positivity
  have ha : 0 ≤ 2 /
      (sigma * Real.sqrt (2 * Real.pi) * ((m : ℝ) ^ 5)) := by positivity
  have hb : 0 ≤ (2 * (n : ℝ)) /
      (sigma * Real.sqrt (2 * Real.pi)) := by positivity
  have hreal : ((n * m ^ 4 : ℕ) : ℝ) *
      (2 / (sigma * Real.sqrt (2 * Real.pi) * ((m : ℝ) ^ 5))) =
      ((2 * (n : ℝ)) / (sigma * Real.sqrt (2 * Real.pi))) / (m : ℝ) := by
    push_cast
    field_simp
  have hnn : (((n * m ^ 4 : ℕ) : ℝ≥0) *
      Real.toNNReal (2 /
        (sigma * Real.sqrt (2 * Real.pi) * ((m : ℝ) ^ 5)))) =
      Real.toNNReal ((2 * (n : ℝ)) /
        (sigma * Real.sqrt (2 * Real.pi))) * (m : ℝ≥0)⁻¹ := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_natCast]
    rw [Real.coe_toNNReal _ ha, Real.coe_toNNReal _ hb]
    simpa only [div_eq_mul_inv] using hreal
  have hmNN : (m : ℝ≥0) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have hcast := congrArg (fun z : ℝ≥0 => (z : ℝ≥0∞)) hnn
  simpa only [ENNReal.coe_mul, ENNReal.coe_natCast,
    ENNReal.coe_inv hmNN] using hcast
