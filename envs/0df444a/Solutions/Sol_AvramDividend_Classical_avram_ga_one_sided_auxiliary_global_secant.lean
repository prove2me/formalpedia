-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_one_sided_auxiliary_global_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:23:51.056676+00:00
-- url     : https://prove2.me/submissions/93317c67-8bd1-4825-bb02-67c3dd69c7d3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (c : ℝ) (hc : 0 < c) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y)
    (x y : ℝ) (hxy : x ≤ y) :
    y - x ≤
      (if y < 0 then w 0 + y else
        if y ≤ c then w y else w c + (y - c)) -
      (if x < 0 then w 0 + x else
        if x ≤ c then w x else w c + (x - c)) := by
  have hV : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      b - a ≤
        (if b ≤ c then w b else w c + (b - c)) -
        (if a ≤ c then w a else w c + (a - c)) := by
    intro a b ha hab
    exact avram_wave4_04_cap_linear_extension_full_secant
      c hc w hw_cont hw_smooth hw_grad a b ha hab
  by_cases hx : x < 0
  · by_cases hy : y < 0
    · simp only [if_pos hx, if_pos hy]
      linarith
    · have hy0 : 0 ≤ y := le_of_not_gt hy
      have h00 : (0 : ℝ) ≤ c := le_of_lt hc
      have hsec := hV 0 y (le_refl _) hy0
      simp only [if_pos h00] at hsec
      simp only [if_neg hy, if_pos hx]
      linarith
  · have hx0 : 0 ≤ x := le_of_not_gt hx
    have hy0 : 0 ≤ y := le_trans hx0 hxy
    have hy : ¬ y < 0 := not_lt.mpr hy0
    simpa only [if_neg hx, if_neg hy] using hV x y hx0 hxy
