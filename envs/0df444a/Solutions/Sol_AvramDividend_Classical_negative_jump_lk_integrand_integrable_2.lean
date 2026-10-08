-- Prove2me | solution 2 for AvramDividend.Classical.negative_jump_lk_integrand_integrable
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T15:22:22.632975+00:00
-- url     : https://prove2.me/submissions/91c486b6-dcc0-4790-8581-7aba0137ab33

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
  have hsub : Iio (0 : ℝ) ⊆ Iic (-1) ∪ Ioo (-1) 0 := by
    intro y hy
    by_cases h : y ≤ -1
    · exact Or.inl h
    · exact Or.inr ⟨by push_neg at h; exact h, hy⟩
  have hmeas : Measurable (fun y : ℝ => Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) := by
    have : Measurable ((Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ)) :=
      measurable_const.indicator measurableSet_Ioo
    fun_prop
  refine IntegrableOn.mono_set ?_ hsub
  refine IntegrableOn.union ?_ ?_
  · haveI : IsFiniteMeasure (ν.restrict (Iic (-1))) := ⟨by simpa using hlarge⟩
    refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
    have hy' : y ∉ Ioo (-1 : ℝ) 1 := fun h => by simp at hy; linarith [h.1]
    rw [Set.indicator_of_notMem hy']
    have h1 : θ * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ (by simp at hy; linarith)
    have h2 := Real.exp_pos (θ * y)
    have h3 : Real.exp (θ * y) ≤ 1 := Real.exp_le_one_iff.mpr h1
    rw [Real.norm_eq_abs, abs_le]; constructor <;> simp <;> linarith
  · have hint : IntegrableOn (fun y : ℝ => θ ^ 2 * y ^ 2) (Ioo (-1) 0) ν := by
      refine Integrable.const_mul ?_ _
      refine ⟨(by fun_prop : Measurable fun y : ℝ => y ^ 2).aestronglyMeasurable, ?_⟩
      unfold HasFiniteIntegral
      convert hsmall using 3 with y
      rw [Real.enorm_eq_ofReal (by positivity)]
    refine Integrable.mono' hint hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hy' : y ∈ Ioo (-1 : ℝ) 1 := ⟨hy.1, by linarith [hy.2]⟩
    rw [Set.indicator_of_mem hy']
    simp only [Pi.one_apply, mul_one]
    have h1 : θ * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ hy.2.le
    have hlow : 0 ≤ Real.exp (θ * y) - 1 - θ * y := by
      linarith [Real.add_one_le_exp (θ * y)]
    rw [Real.norm_eq_abs, abs_of_nonneg hlow, ← mul_pow]
    by_cases hx : |θ * y| ≤ 1
    · have := Real.abs_exp_sub_one_sub_id_le hx
      exact (le_abs_self _).trans this
    · push_neg at hx
      rw [abs_of_nonpos h1] at hx
      have h3 : Real.exp (θ * y) ≤ 1 := Real.exp_le_one_iff.mpr h1
      nlinarith
