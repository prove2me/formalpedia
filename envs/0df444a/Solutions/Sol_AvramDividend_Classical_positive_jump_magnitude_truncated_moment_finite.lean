-- Prove2me | solution 1 for AvramDividend.Classical.positive_jump_magnitude_truncated_moment_finite
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T04:27:13.119779+00:00
-- url     : https://prove2.me/submissions/048043ec-ae0e-454c-a3cd-d42294471c3c

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

open MeasureTheory Set NNReal ENNReal in
theorem solution (ν : Measure ℝ)
    (hsmall : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂ν) ≠ ⊤)
    (hquad : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) ≠ ⊤) :
    (∫⁻ z : ℝ≥0, ENNReal.ofReal (min (z : ℝ) 1) ∂
      Measure.map (fun y : ℝ => Real.toNNReal (-y)) ν) ≠ ⊤ := by
  have hmeasf : Measurable (fun y : ℝ => Real.toNNReal (-y)) := by
    fun_prop
  have hmeasg : Measurable (fun z : ℝ≥0 => ENNReal.ofReal (min (z : ℝ) 1)) := by
    fun_prop
  have hmeas : Measurable (fun y : ℝ => ENNReal.ofReal (min 1 (y ^ 2))) := by
    fun_prop
  rw [lintegral_map hmeasg hmeasf]
  have hpt : ∀ y : ℝ, ENNReal.ofReal (min ((Real.toNNReal (-y) : ℝ≥0) : ℝ) 1) ≤
      ENNReal.ofReal (min 1 (y ^ 2)) +
        (Ioo (-1 : ℝ) 0).indicator (fun y => ENNReal.ofReal |y|) y := by
    intro y
    rw [Real.coe_toNNReal']
    by_cases h0 : 0 ≤ y
    · have : max (-y) 0 = 0 := max_eq_right (by linarith)
      rw [this, min_eq_left zero_le_one, ENNReal.ofReal_zero]
      exact bot_le
    · have hy0 : y < 0 := lt_of_not_ge h0
      have hm : max (-y) 0 = -y := max_eq_left (by linarith)
      rw [hm]
      by_cases h1 : y ≤ -1
      · apply le_add_right
        apply ENNReal.ofReal_le_ofReal
        have : (1 : ℝ) ≤ y ^ 2 := by nlinarith
        have h2 : min 1 (y ^ 2) = 1 := min_eq_left this
        rw [h2]
        exact min_le_right _ _
      · replace h1 : -1 < y := lt_of_not_ge h1
        rw [indicator_of_mem (show y ∈ Ioo (-1 : ℝ) 0 from ⟨h1, hy0⟩)]
        apply le_add_left
        apply ENNReal.ofReal_le_ofReal
        exact (min_le_left _ _).trans (neg_le_abs y)
  apply ne_top_of_le_ne_top _ (lintegral_mono hpt)
  rw [lintegral_add_left hmeas, lintegral_indicator measurableSet_Ioo]
  exact ENNReal.add_ne_top.2 ⟨hquad, hsmall⟩
