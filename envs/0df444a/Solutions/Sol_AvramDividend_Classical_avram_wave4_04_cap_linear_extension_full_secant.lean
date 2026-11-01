-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_cap_linear_extension_full_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:11:48.215612+00:00
-- url     : https://prove2.me/submissions/abbd59a8-4e31-4538-8f86-76c429064bf1

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The slope-one continuation preserves every dividend secant, including cap contact. -/
theorem solution
    (c : ℝ) (hc : 0 < c) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    b - a ≤
      (if b ≤ c then w b else w c + (b - c)) -
      (if a ≤ c then w a else w c + (a - c)) := by
  have hC : (0 : ℝ≥0∞) < ENNReal.ofReal c :=
    ENNReal.ofReal_pos.mpr hc
  have hsec (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hvc : v ≤ c) :
      v - u ≤ w v - w u := by
    exact avram_wave3_03_bv_full_cap_gradient_secant
      (ENNReal.ofReal c) hC w hw_cont hw_smooth hw_grad
      u v hu huv (ENNReal.ofReal_le_ofReal hvc)
  by_cases hbc : b ≤ c
  · have hac : a ≤ c := le_trans hab hbc
    simpa [if_pos hbc, if_pos hac] using hsec a b ha hab hbc
  · by_cases hac : a ≤ c
    · have hs := hsec a c ha hac le_rfl
      simp only [if_neg hbc, if_pos hac]
      linarith
    · simp [if_neg hbc, if_neg hac]