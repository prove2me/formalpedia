-- Prove2me | solution 3 for AvramDividend.Classical.negative_jump_lk_integrand_integrable
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T17:30:50.845802+00:00
-- url     : https://prove2.me/submissions/892b31ac-9fdd-47b4-bd4f-1e60c66484e7

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (ν : Measure ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hsmall : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal (y ^ 2) ∂ν) < ⊤)
    (hlarge : ν (Iic (-1 : ℝ)) < ⊤) :
    IntegrableOn
      (fun y : ℝ => Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y)
      (Iio (0 : ℝ)) ν := by
  have hmeas : Measurable (fun y : ℝ => Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) := by
    have : Measurable ((Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ)) :=
      measurable_const.indicator measurableSet_Ioo
    fun_prop
  have hsplit : Iio (0 : ℝ) = Iic (-1) ∪ Ioo (-1) 0 := by
    ext y; simp only [mem_Iio, mem_union, mem_Iic, mem_Ioo]; constructor
    · intro h; by_cases h1 : y ≤ -1
      · exact Or.inl h1
      · exact Or.inr ⟨by linarith, h⟩
    · rintro (h | h)
      · linarith
      · exact h.2
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · refine Measure.integrableOn_of_bounded (M := 1) hlarge.ne hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Iic).2 (Filter.Eventually.of_forall fun y hy => ?_)
    have hy' : y ∉ Ioo (-1 : ℝ) 1 := fun h => by simp only [mem_Iic] at hy; linarith [h.1]
    simp only [Set.indicator_of_notMem hy', mul_zero, sub_zero, Real.norm_eq_abs]
    have h1 : θ * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ (by simp only [mem_Iic] at hy; linarith)
    have h2 := Real.exp_le_one_iff.2 h1
    have h3 := Real.exp_pos (θ * y)
    rw [abs_le]; constructor <;> linarith
  · have hg : IntegrableOn (fun y : ℝ => θ ^ 2 * y ^ 2) (Ioo (-1) 0) ν := by
      refine Integrable.const_mul ?_ _
      refine ⟨by fun_prop, ?_⟩
      unfold HasFiniteIntegral
      refine lt_of_le_of_lt (le_of_eq ?_) hsmall
      refine lintegral_congr fun y => ?_
      rw [Real.enorm_of_nonneg (sq_nonneg y)]
    refine hg.mono' hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun y hy => ?_)
    have hy' : y ∈ Ioo (-1 : ℝ) 1 := ⟨hy.1, by linarith [hy.2]⟩
    simp only [Set.indicator_of_mem hy', Pi.one_apply, mul_one, Real.norm_eq_abs]
    set x := θ * y with hx
    have hx0 : x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ hy.2.le
    have hlo := Real.add_one_le_exp x
    have hq := Real.quadratic_le_exp_of_nonneg (x := -x) (by linarith)
    have hprod : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos x
    have hup : Real.exp x ≤ 1 + x + x ^ 2 / 2 := by
      nlinarith [sq_nonneg x, sq_nonneg (x^2), mul_le_mul_of_nonneg_left hq hpos.le]
    have : θ ^ 2 * y ^ 2 = x ^ 2 := by rw [hx]; ring
    rw [this, abs_le]; constructor <;> nlinarith [sq_nonneg x]
