-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_complement_positive_horizon_and_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:26:02.335224+00:00
-- url     : https://prove2.me/submissions/8dbb1aed-c8aa-4b33-822e-9393a729d5ac

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (T drift : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * drift ≤ w x)) :
    0 < T ∧ 0 < drift := by
  have hGradient := avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
    C hC w hw_cont hw_smooth hw_grad x hx hxc
  have hWx : w 0 + x ≤ w x := hGradient x ⟨hx, le_refl x⟩
  have hStrict : w x < x + T * drift := lt_of_not_ge hEnvelope
  have hProduct : 0 < T * drift := by linarith only [hWx, hw0, hStrict]
  constructor
  · by_contra hNot
    have hZero : T = 0 := le_antisymm (le_of_not_gt hNot) hT
    simp [hZero] at hProduct
  · by_contra hNot
    have hd : drift ≤ 0 := le_of_not_gt hNot
    have hNonpos : T * drift ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hT hd
    exact (not_le_of_gt hProduct) hNonpos
