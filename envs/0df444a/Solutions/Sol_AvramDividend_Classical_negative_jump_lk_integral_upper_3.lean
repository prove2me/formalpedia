-- Prove2me | solution 3 for AvramDividend.Classical.negative_jump_lk_integral_upper
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T17:15:49.942979+00:00
-- url     : https://prove2.me/submissions/0b480517-009e-49dc-8437-1d3b11e8da7a

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (ν : Measure ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hint : IntegrableOn
      (fun y : ℝ => Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y)
      (Iio (0 : ℝ)) ν)
    (hy2 : IntegrableOn (fun y : ℝ => y ^ 2) (Ioo (-1 : ℝ) 0) ν) :
    (∫ y in Iio (0 : ℝ),
      (Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂ν) ≤
      θ ^ 2 * ∫ y in Ioo (-1 : ℝ) 0, y ^ 2 ∂ν := by
  have hg : IntegrableOn (fun y : ℝ => (Ioo (-1 : ℝ) 0).indicator
      (fun y => θ ^ 2 * y ^ 2) y) (Iio (0 : ℝ)) ν := by
    have : Integrable (fun y : ℝ => (Ioo (-1 : ℝ) 0).indicator
        (fun y => θ ^ 2 * y ^ 2) y) ν :=
      (integrable_indicator_iff measurableSet_Ioo).2 (hy2.const_mul _)
    exact this.integrableOn
  have key : ∫ y in Iio (0 : ℝ), (Ioo (-1 : ℝ) 0).indicator
      (fun y => θ ^ 2 * y ^ 2) y ∂ν = θ ^ 2 * ∫ y in Ioo (-1 : ℝ) 0, y ^ 2 ∂ν := by
    rw [setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.2 Ioo_subset_Iio_self, integral_const_mul]
  rw [← key]
  refine setIntegral_mono_on hint hg measurableSet_Iio (fun y hy => ?_)
  have hy0 : y < 0 := hy
  have hx : θ * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ hy0.le
  by_cases h1 : -1 < y
  · have hm : y ∈ Ioo (-1 : ℝ) 1 := ⟨h1, by linarith⟩
    have hm' : y ∈ Ioo (-1 : ℝ) 0 := ⟨h1, hy0⟩
    simp only [indicator_of_mem hm, indicator_of_mem hm', Pi.one_apply, mul_one]
    by_cases hb : -1 ≤ θ * y
    · have h2 := Real.abs_exp_sub_one_sub_id_le (x := θ * y)
        (by rw [abs_le]; constructor <;> linarith)
      have h3 := (abs_le.1 h2).2
      nlinarith [h3]
    · push_neg at hb
      have h4 := Real.exp_le_one_iff.2 hx
      nlinarith [mul_pos_of_neg_of_neg (by linarith : θ * y < 0)
        (by linarith : θ * y + 1 < 0)]
  · have hm : y ∉ Ioo (-1 : ℝ) 1 := fun h => h1 h.1
    have hm' : y ∉ Ioo (-1 : ℝ) 0 := fun h => h1 h.1
    simp only [indicator_of_notMem hm, indicator_of_notMem hm', mul_zero, sub_zero]
    have h4 := Real.exp_le_one_iff.2 hx
    linarith
