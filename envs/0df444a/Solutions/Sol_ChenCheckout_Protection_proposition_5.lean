-- Prove2me | solution 1 for ChenCheckout.Protection.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T07:51:57.326476+00:00
-- url     : https://prove2.me/submissions/cf658018-55fc-4e19-bcfa-7f1e7892aec8

import Mathlib

open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc 0 b)
    (hmean : b/2 ≤ ∫ ω, X ω ∂μ) (a : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    a/2 ≤ ∫ ω, min (X ω) a ∂μ := by
  have hXi : Integrable X μ := by
    refine Integrable.of_bound hX.aestronglyMeasurable b ?_
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω.1]; exact hω.2
  have hMi : Integrable (fun ω => min (X ω) a) μ := by
    refine Integrable.of_bound (hX.min measurable_const).aestronglyMeasurable b ?_
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hω.1 ha)]
    exact (min_le_left _ _).trans hω.2
  have hpt : ∀ᵐ ω ∂μ, a * X ω ≤ b * min (X ω) a := by
    filter_upwards [hbound] with ω hω
    rcases le_total (X ω) a with h | h
    · rw [min_eq_left h]; exact mul_le_mul_of_nonneg_right hab hω.1
    · rw [min_eq_right h]
      calc a * X ω ≤ a * b := mul_le_mul_of_nonneg_left hω.2 ha
        _ = b * a := mul_comm _ _
  have hint : a * ∫ ω, X ω ∂μ ≤ b * ∫ ω, min (X ω) a ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul]
    exact integral_mono_ae (hXi.const_mul a) (hMi.const_mul b) hpt
  have hnn : 0 ≤ ∫ ω, min (X ω) a ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hbound] with ω hω
    exact le_min hω.1 ha
  rcases hb.lt_or_eq with hb' | hb'
  · have h1 : a * (b / 2) ≤ a * ∫ ω, X ω ∂μ := mul_le_mul_of_nonneg_left hmean ha
    have : b * (a / 2) ≤ b * ∫ ω, min (X ω) a ∂μ := by nlinarith
    exact le_of_mul_le_mul_left this hb'
  · have : a = 0 := le_antisymm (hb' ▸ hab) ha
    subst this; simpa using hnn
