-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_ubv_zero_reserve_real_perpetual_cash_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:39:22.831553+00:00
-- url     : https://prove2.me/submissions/0a58faac-165a-4bc6-8f35-bb43ceec03e8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_ubv_original_zero_start_capped_valueFunctionLe_upper
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The genuine original zero-reserve UBV strategy has an L1 real perpetual
Stieltjes payout bounded in expected value by the HJB boundary value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 C D) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X 0 D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    (∫ ω, (∫ t in paymentTimes (ruinTime X 0 D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ w 0 := by
  have hValueLe : dividendValue X q 0 D ≤ valueFunctionLe X q C 0 := by
    unfold valueFunctionLe
    exact le_iSup_of_le D (le_iSup_of_le hD le_rfl)
  have hZeroBound : valueFunctionLe X q C 0 ≤ ENNReal.ofReal (w 0) :=
    avram_wave6_10_ubv_original_zero_start_capped_valueFunctionLe_upper
      X hBV q w C hw0 hw_cont hw_smooth hw_hjb
  have hValueBound : dividendValue X q 0 D ≤ ENNReal.ofReal (w 0) :=
    hValueLe.trans hZeroBound
  have hFinite : dividendValue X q 0 D < ⊤ :=
    lt_of_le_of_lt hValueBound ENNReal.ofReal_lt_top
  obtain ⟨hIntegrable, hIdentity⟩ :=
    avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
      X 0 D hD.1.1 q hFinite
  refine ⟨hIntegrable, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hw0).mp
  simpa only [hIdentity] using hValueBound
