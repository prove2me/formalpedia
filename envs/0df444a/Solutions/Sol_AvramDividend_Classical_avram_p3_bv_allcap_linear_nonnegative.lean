-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_allcap_linear_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:46:10.945941+00:00
-- url     : https://prove2.me/submissions/ea6cc399-7dde-45f1-bb0f-cb2e9b20eaf9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_allcap_linear_monotone_nonnegative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- Original HJB candidate positivity propagates through the cap-linear
continuation to every nonnegative reserve, including cap contacts. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (z : ℝ) (hz : 0 ≤ z) :
    0 ≤ (if C = ⊤ then w z
      else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)) := by
  let V : ℝ → ℝ := fun y =>
    if C = ⊤ then w y
    else if y ≤ C.toReal then w y
    else w C.toReal + (y - C.toReal)
  have hmono := avram_p3_bv_allcap_linear_monotone_nonnegative
    C hC w hw_cont hw_smooth hw_grad
  change MonotoneOn V (Ici 0) at hmono
  have hV0 : V 0 = w 0 := by
    dsimp [V]
    by_cases htop : C = ⊤
    · simp [htop]
    · have hC0 : 0 ≤ C.toReal := ENNReal.toReal_nonneg
      simp [htop, hC0]
  have hle : V 0 ≤ V z := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hz) hz
  change 0 ≤ V z
  linarith
