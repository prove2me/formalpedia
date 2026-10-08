-- Prove2me | solution 1 for AvramDividend.Classical.exp_compensated_integral_lower_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T20:32:16.782671+00:00
-- url     : https://prove2.me/submissions/6b6d5c34-223e-4dc2-b60c-9fd51c6ec999

import Mathlib

open MeasureTheory Set

theorem solution
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (θ : ℝ) (hθ : 0 ≤ θ)
    (hneg : ∀ᵐ y ∂ν, y ≤ 0)
    (hyint : Integrable (fun y : ℝ => y) ν) :
    (∫ y : ℝ, θ * |y| - 1 ∂ν) ≤
      ∫ y : ℝ, (Real.exp (θ * y) - 1 - θ * y) ∂ν := by
  have hexp_meas :
      AEStronglyMeasurable (fun y : ℝ => Real.exp (θ * y)) ν := by
    fun_prop
  have hexp_int :
      Integrable (fun y : ℝ => Real.exp (θ * y)) ν := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) hexp_meas
    filter_upwards [hneg] with y hy
    have hz : θ * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ hy
    have he : Real.exp (θ * y) ≤ 1 :=
      Real.exp_le_one_iff.mpr hz
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using he
  have hleft :
      Integrable (fun y : ℝ => θ * |y| - 1) ν :=
    (hyint.abs.const_mul θ).sub (integrable_const (1 : ℝ))
  have hright :
      Integrable (fun y : ℝ => Real.exp (θ * y) - 1 - θ * y) ν :=
    (hexp_int.sub (integrable_const (1 : ℝ))).sub (hyint.const_mul θ)
  apply integral_mono_ae hleft hright
  filter_upwards [hneg] with y hy
  rw [abs_of_nonpos hy]
  linarith [Real.exp_pos (θ * y)]
