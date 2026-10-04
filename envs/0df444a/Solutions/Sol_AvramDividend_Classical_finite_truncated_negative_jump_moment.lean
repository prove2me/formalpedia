-- Prove2me | solution 1 for AvramDividend.Classical.finite_truncated_negative_jump_moment
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T00:32:35.794376+00:00
-- url     : https://prove2.me/submissions/b5c06a1c-6f23-47cd-b6ed-def83f7b7f1f

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

open MeasureTheory Set in
theorem solution (ν : Measure ℝ)
    (hν : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤)
    (hBV : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂ν) < ⊤) :
    (∫⁻ y in Iio (0 : ℝ),
      ENNReal.ofReal (min (-y) 1) ∂ν) < ⊤ := by
  have hmeas : Measurable (fun y : ℝ => ENNReal.ofReal (min 1 (y ^ 2))) := by
    fun_prop
  have hpt : ∀ y ∈ Iio (0 : ℝ), ENNReal.ofReal (min (-y) 1) ≤
      ENNReal.ofReal (min 1 (y ^ 2)) +
        (Ioo (-1 : ℝ) 0).indicator (fun y => ENNReal.ofReal |y|) y := by
    intro y hy
    have hy0 : y < 0 := hy
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
  calc (∫⁻ y in Iio (0 : ℝ), ENNReal.ofReal (min (-y) 1) ∂ν)
      ≤ ∫⁻ y in Iio (0 : ℝ), (ENNReal.ofReal (min 1 (y ^ 2)) +
          (Ioo (-1 : ℝ) 0).indicator (fun y => ENNReal.ofReal |y|) y) ∂ν :=
        setLIntegral_mono' measurableSet_Iio hpt
    _ ≤ ∫⁻ y, (ENNReal.ofReal (min 1 (y ^ 2)) +
          (Ioo (-1 : ℝ) 0).indicator (fun y => ENNReal.ofReal |y|) y) ∂ν :=
        setLIntegral_le_lintegral _ _
    _ = (∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) +
          ∫⁻ y, (Ioo (-1 : ℝ) 0).indicator (fun y => ENNReal.ofReal |y|) y ∂ν :=
        lintegral_add_left hmeas _
    _ = (∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) +
          ∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂ν := by
        rw [lintegral_indicator measurableSet_Ioo]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hν, hBV⟩
