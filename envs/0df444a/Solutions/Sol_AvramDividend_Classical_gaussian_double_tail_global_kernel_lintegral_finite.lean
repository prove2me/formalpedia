-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_global_kernel_lintegral_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T12:11:15.224711+00:00
-- url     : https://prove2.me/submissions/5c221635-df13-4224-ba21-a695757015d1

import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_global_area_tonelli
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_damped_quadratic_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution (μ : Measure ℝ) [SFinite μ]
    (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ t : ℝ, ∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) *
          ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂μ ∂volume) < ⊤ := by
  have hdamp :
      (∫⁻ z in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(φ * z)) * z ^ 2) ∂μ) < ⊤ :=
    gaussian_esscher_damped_quadratic_integrable μ φ hφ hlevy
  rw [gaussian_double_tail_global_area_tonelli μ φ]
  apply lt_of_le_of_lt (lintegral_mono (fun z => ?_)) hdamp
  have hzsq : 0 ≤ z ^ 2 := sq_nonneg z
  have hzhalf : z ^ 2 / 2 ≤ z ^ 2 := by nlinarith
  have he : 0 ≤ Real.exp (-(φ * z)) := (Real.exp_pos _).le
  have hbound : Real.exp (-(φ * z)) * (z ^ 2 / 2) ≤
      Real.exp (-(φ * z)) * z ^ 2 :=
    mul_le_mul_of_nonneg_left hzhalf he
  calc
    ENNReal.ofReal (z ^ 2 / 2) *
        ENNReal.ofReal (Real.exp (-(φ * z))) =
      ENNReal.ofReal (Real.exp (-(φ * z)) * (z ^ 2 / 2)) := by
        rw [ENNReal.ofReal_mul he]
        exact mul_comm _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(φ * z)) * z ^ 2) :=
      ENNReal.ofReal_le_ofReal hbound
