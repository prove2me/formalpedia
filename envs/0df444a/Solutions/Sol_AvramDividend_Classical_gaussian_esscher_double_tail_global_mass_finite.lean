-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_double_tail_global_mass_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T12:13:46.253594+00:00
-- url     : https://prove2.me/submissions/124a5d80-5488-4e7f-9b4d-100fbc093af2

import Mathlib.Tactic
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_global_area_tonelli
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_damped_quadratic_integrable

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Global Gaussian double-tail mass is bounded by the damped quadratic jump moment. -/
theorem solution
    (μ : Measure ℝ) [SFinite μ]
    (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ t : ℝ, ∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) *
          ENNReal.ofReal (Real.exp (-(φ * z)))
       else 0) ∂μ ∂volume) < ⊤ := by
  have hpoint (z : ℝ) :
      ENNReal.ofReal (z ^ 2 / 2) *
          ENNReal.ofReal (Real.exp (-(φ * z))) ≤
        ENNReal.ofReal (Real.exp (-(φ * z)) * z ^ 2) := by
    have hnonneg : 0 ≤ z ^ 2 / 2 := by positivity
    have hhalf : z ^ 2 / 2 ≤ z ^ 2 := by
      nlinarith only [sq_nonneg z]
    have hreal :
        (z ^ 2 / 2) * Real.exp (-(φ * z)) ≤
          Real.exp (-(φ * z)) * z ^ 2 := by
      calc
        _ ≤ z ^ 2 * Real.exp (-(φ * z)) :=
          mul_le_mul_of_nonneg_right hhalf (Real.exp_pos _).le
        _ = _ := mul_comm _ _
    rw [← ENNReal.ofReal_mul hnonneg]
    exact ENNReal.ofReal_le_ofReal hreal
  have hbound :
      (∫⁻ z in Ioi (0 : ℝ),
        ENNReal.ofReal (z ^ 2 / 2) *
          ENNReal.ofReal (Real.exp (-(φ * z))) ∂μ) ≤
      (∫⁻ z in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(φ * z)) * z ^ 2) ∂μ) :=
    lintegral_mono hpoint
  rw [gaussian_double_tail_global_area_tonelli μ φ]
  exact lt_of_le_of_lt hbound
    (gaussian_esscher_damped_quadratic_integrable μ φ hφ hlevy)
