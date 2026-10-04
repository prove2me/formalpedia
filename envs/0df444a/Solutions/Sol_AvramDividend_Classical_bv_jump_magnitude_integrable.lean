-- Prove2me | solution 1 for AvramDividend.Classical.bv_jump_magnitude_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T00:35:12.229514+00:00
-- url     : https://prove2.me/submissions/1886d3dc-1d77-47dd-8b8a-7be6d50da198

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal

set_option autoImplicit false

lemma avram47_pointwise (y : ℝ) :
    ENNReal.ofReal (min ((Real.toNNReal (-y) : ℝ≥0) : ℝ) 1) ≤
      ENNReal.ofReal (min 1 (y ^ 2)) +
        (Ioo (-1 : ℝ) 0).indicator (fun y => ENNReal.ofReal |y|) y := by
  rw [Real.coe_toNNReal']
  by_cases hy : 0 ≤ y
  · have : max (-y) 0 = 0 := by
      rw [max_eq_right]; linarith
    rw [this, min_eq_left (by norm_num : (0:ℝ) ≤ 1), ENNReal.ofReal_zero]
    exact bot_le
  · replace hy : y < 0 := not_le.mp hy
    have hm : max (-y) 0 = -y := max_eq_left (by linarith)
    rw [hm]
    by_cases h1 : -1 < y
    · have hmem : y ∈ Ioo (-1 : ℝ) 0 := ⟨h1, hy⟩
      rw [indicator_of_mem hmem, abs_of_neg hy, min_eq_left (by linarith)]
      exact le_add_self
    · replace h1 : y ≤ -1 := not_lt.mp h1
      have hsq : 1 ≤ y ^ 2 := by nlinarith
      rw [min_eq_right (by linarith), min_eq_left hsq]
      exact le_self_add

open MeasureTheory Set NNReal ENNReal AvramDividend.Classical in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    (∫⁻ z : ℝ≥0, ENNReal.ofReal (min (z : ℝ) 1)
      ∂ ((X.ν.restrict (Iio (0 : ℝ))).map
          (fun y : ℝ => Real.toNNReal (-y)))) < ⊤ := by
  have hg : Measurable (fun y : ℝ => Real.toNNReal (-y)) :=
    measurable_real_toNNReal.comp measurable_neg
  have hf : Measurable (fun z : ℝ≥0 => ENNReal.ofReal (min (z : ℝ) 1)) := by
    fun_prop
  rw [lintegral_map hf hg]
  calc ∫⁻ y in Iio (0 : ℝ), ENNReal.ofReal (min ((Real.toNNReal (-y) : ℝ≥0) : ℝ) 1) ∂X.ν
      ≤ ∫⁻ y, ENNReal.ofReal (min ((Real.toNNReal (-y) : ℝ≥0) : ℝ) 1) ∂X.ν :=
        setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ y, (ENNReal.ofReal (min 1 (y ^ 2)) +
          (Ioo (-1 : ℝ) 0).indicator (fun y => ENNReal.ofReal |y|) y) ∂X.ν :=
        lintegral_mono (fun y => avram47_pointwise y)
    _ = ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν +
          ∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν := by
        rw [lintegral_add_right _ ((Measurable.ennreal_ofReal measurable_abs).indicator
          measurableSet_Ioo), lintegral_indicator measurableSet_Ioo]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨X.ν_integrable, hBV.2⟩
