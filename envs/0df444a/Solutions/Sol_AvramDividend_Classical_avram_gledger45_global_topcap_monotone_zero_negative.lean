-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger45_global_topcap_monotone_zero_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T20:17:33.487376+00:00
-- url     : https://prove2.me/submissions/1416d0cb-88ff-4f2e-ba29-27b9423b1d8c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger29_topcap_secant_without_contdiff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A negative source jump at ruin cannot reverse the top-cap reward order. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (a b : ℝ) (hab : a ≤ b) : w a ≤ w b := by
  have hgrad : ∀ y : ℝ, 0 < y → 1 ≤ deriv w y := by
    intro y hy
    exact hw_grad y hy (by simp [hTopCap])
  by_cases ha : 0 ≤ a
  · have hs := avram_gledger29_topcap_secant_without_contdiff
      w hw_cont hgrad a b ha hab
    linarith
  by_cases hb : 0 ≤ b
  · have hs := avram_gledger29_topcap_secant_without_contdiff
      w hw_cont hgrad 0 b le_rfl hb
    rw [hw_neg a (lt_of_not_ge ha)]
    linarith
  · rw [hw_neg a (lt_of_not_ge ha), hw_neg b (lt_of_not_ge hb)]
