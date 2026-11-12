-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite79_original_cap_slack
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:00:43.274237+00:00
-- url     : https://prove2.me/submissions/72012589-77e8-410f-a481-c0b68777bfcf

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gfinite78_cap_gap_of_C2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The physical finite cap's fractional cutoff inherits nonnegative cash
    slack directly from the original generator-candidate hypotheses. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (j : ℕ) :
    0 ≤ (w C.toReal - w (C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))) -
      (C.toReal - C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))) := by
  have hcap : 0 < C.toReal := ENNReal.toReal_pos (ne_of_gt hC) hFiniteCap
  let r : ℝ := ((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrlt : r < 1 := by
    dsimp [r]
    apply (div_lt_one (by positivity)).2
    exact_mod_cast (show j + 1 < j + 2 by omega)
  let b : ℝ := C.toReal * r
  have hbpos : 0 < b := mul_pos hcap hrpos
  have hble : b ≤ C.toReal :=
    le_of_lt (mul_lt_of_lt_one_right hcap hrlt)
  have hsmall : Ioo b C.toReal ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro z hz
    have hzpos : 0 < z := lt_trans hbpos hz.1
    exact ⟨hzpos,
      (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hzpos) hFiniteCap).2 hz.2⟩
  have hcont : ContinuousOn w (Icc b C.toReal) := by
    apply hw_cont.mono
    intro z hz
    exact le_trans (le_of_lt hbpos) hz.1
  have hsmooth : ContDiffOn ℝ 2 w (Ioo b C.toReal) := hw_smooth.mono hsmall
  have hgrad : ∀ z ∈ Ioo b C.toReal, 1 ≤ deriv w z := by
    intro z hz
    exact hw_grad z (hsmall hz).1 (hsmall hz).2
  have hmain := avram_gfinite78_cap_gap_of_C2 w b C.toReal hble hcont hsmooth hgrad
  simpa [b, r] using hmain
