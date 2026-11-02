-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_C1_jump_increment_integrated_uniform_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:10:29.520329+00:00
-- url     : https://prove2.me/submissions/e976a778-6d18-4e42-9488-f9fcc07f3bce

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_negative_jump_increment_FTC
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set
open AvramDividend.Classical

/-! Quantitative weighted first-moment error when replacing an integrated
C1 jump derivative by any continuous approximant on a residual band. -/
theorem solution (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (f : ℝ → ℝ) (hf : Continuous f)
    (y R ε : ℝ) (hR : 0 ≤ R)
    (herror : ∀ r ∈ uIoc (0 : ℝ) R,
      |deriv w (y - r) - f r| ≤ ε) :
    |(w y - w (y - R)) - (∫ r in (0 : ℝ)..R, f r)| ≤ ε * R := by
  have hcont : Continuous (fun r : ℝ => deriv w (y - r)) :=
    (hwC1.continuous_deriv (by norm_num)).comp
      (continuous_const.sub continuous_id)
  have hI1 : IntervalIntegrable (fun r : ℝ => deriv w (y - r)) volume 0 R :=
    hcont.intervalIntegrable _ _
  have hI2 : IntervalIntegrable f volume 0 R := hf.intervalIntegrable _ _
  have hbound :
      ‖∫ r in (0 : ℝ)..R, deriv w (y - r) - f r‖ ≤
        ε * |R - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    simpa only [Real.norm_eq_abs] using herror t ht
  calc
    |(w y - w (y - R)) - (∫ r in (0 : ℝ)..R, f r)| =
        |(∫ r in (0 : ℝ)..R, deriv w (y - r)) -
          (∫ r in (0 : ℝ)..R, f r)| := by
            rw [avram_wave5_04c_C1_negative_jump_increment_FTC w hwC1 y R]
    _ = |∫ r in (0 : ℝ)..R, deriv w (y - r) - f r| := by
          rw [intervalIntegral.integral_sub hI1 hI2]
    _ ≤ ε * R := by
          simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hR] using hbound
