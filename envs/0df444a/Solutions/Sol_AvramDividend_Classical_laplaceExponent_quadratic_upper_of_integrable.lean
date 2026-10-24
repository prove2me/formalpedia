-- Prove2me | solution 1 for AvramDividend.Classical.laplaceExponent_quadratic_upper_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:06:37.212169+00:00
-- url     : https://prove2.me/submissions/b0a606ca-f9cc-40ab-8903-7d143541526f

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_negative_jump_lk_integral_upper
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The Gaussian and drift terms preserve the proved quadratic bound on jumps. -/
theorem solution
    (c σ : ℝ) (ν : Measure ℝ) (θ : ℝ) (hθ : 1 ≤ θ)
    (hint : IntegrableOn
      (fun y : ℝ => Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y)
      (Iio (0 : ℝ)) ν)
    (hy2 : IntegrableOn (fun y : ℝ => y ^ 2)
      (Ioo (-1 : ℝ) 0) ν) :
    laplaceExponent c σ ν θ ≤
      (|c| + σ ^ 2 / 2 +
        ∫ y in Ioo (-1 : ℝ) 0, y ^ 2 ∂ν) * θ ^ 2 := by
  have hθ0 : 0 ≤ θ := by linarith
  have hθsq : θ ≤ θ ^ 2 := by
    nlinarith [mul_nonneg hθ0 (sub_nonneg.mpr hθ)]
  have hdrift : c * θ ≤ |c| * θ ^ 2 := by
    calc
      c * θ ≤ |c| * θ :=
        mul_le_mul_of_nonneg_right (le_abs_self c) hθ0
      _ ≤ |c| * θ ^ 2 :=
        mul_le_mul_of_nonneg_left hθsq (abs_nonneg c)
  have hjump := negative_jump_lk_integral_upper ν θ hθ0 hint hy2
  unfold laplaceExponent
  nlinarith
