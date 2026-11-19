-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_anycap_initial_rightpayment_postvalue_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:46:35.138093+00:00
-- url     : https://prove2.me/submissions/78accf6b-c1fb-4f2b-82ca-83f343b9d5cf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_closed_cap_actual_right_discounted_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (q : ℝ) (ω : Ω) :
    rightLimit D 0 ω + w (x - rightLimit D 0 ω) - w x ≤ 0 := by
  have h :=
    avram_p4_d_dividend_closed_cap_actual_right_discounted_nonpos
      X x C hC hxc D hD w hw_cont hw_smooth hw_grad q ω 0 (Or.inl rfl)
  have hD0 : D 0 ω = 0 := hD.1.1.1 ω
  have hX0 : X.X 0 ω = 0 := X.X_zero ω
  simpa [riskProcess, hD0, hX0] using h
