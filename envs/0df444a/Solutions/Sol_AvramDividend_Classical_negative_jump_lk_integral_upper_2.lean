-- Prove2me | solution 2 for AvramDividend.Classical.negative_jump_lk_integral_upper
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T14:52:26.594552+00:00
-- url     : https://prove2.me/submissions/7451df5e-f6cc-4fd1-ad72-52cd6ae08e44

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
  have hsub : Ioo (-1 : ℝ) 0 ⊆ Iio 0 := fun y hy => hy.2
  have hg : IntegrableOn (fun y : ℝ => θ ^ 2 * (Ioo (-1 : ℝ) 0).indicator (fun y => y ^ 2) y)
      (Iio 0) ν := by
    have := (hy2.integrable_indicator measurableSet_Ioo).const_mul (θ ^ 2)
    exact this.integrableOn
  calc (∫ y in Iio (0 : ℝ),
      (Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂ν)
      ≤ ∫ y in Iio (0 : ℝ), θ ^ 2 * (Ioo (-1 : ℝ) 0).indicator (fun y => y ^ 2) y ∂ν := by
        refine setIntegral_mono_on hint hg measurableSet_Iio ?_
        intro y hy
        have hy0 : y < 0 := hy
        by_cases h1 : y ∈ Ioo (-1 : ℝ) 0
        · have h1' : y ∈ Ioo (-1 : ℝ) 1 := ⟨h1.1, by linarith [h1.2]⟩
          rw [indicator_of_mem h1', indicator_of_mem h1]
          simp only [Pi.one_apply, mul_one]
          set x := θ * y
          have hx : x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ hy0.le
          have hxx : θ ^ 2 * y ^ 2 = x ^ 2 := by ring
          rw [hxx]
          by_cases hb : |x| ≤ 1
          · have := Real.abs_exp_sub_one_sub_id_le hb
            linarith [le_abs_self (Real.exp x - 1 - x)]
          · have : x < -1 := by
              rw [abs_of_nonpos hx] at hb; linarith
            have := Real.exp_le_one_iff.mpr hx
            nlinarith
        · have hyle : y ≤ -1 := by
            by_contra h; exact h1 ⟨by linarith, hy0⟩
          have h1' : y ∉ Ioo (-1 : ℝ) 1 := fun h => by linarith [h.1]
          rw [indicator_of_notMem h1', indicator_of_notMem h1]
          have := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hθ hy0.le)
          simp only [mul_zero, sub_zero]; linarith
    _ = θ ^ 2 * ∫ y in Ioo (-1 : ℝ) 0, y ^ 2 ∂ν := by
        rw [integral_const_mul, setIntegral_indicator measurableSet_Ioo,
          inter_eq_right.mpr hsub]
