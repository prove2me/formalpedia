-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss_top14_original_bounded_stop_masked_strict_reward_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:07:59.097722+00:00
-- url     : https://prove2.me/submissions/e5e4aac0-c6fb-4ef3-8501-1cb774321c4b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss_top14_original_bounded_stop_prepayment_terminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_bounded_stopped_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_rightcont_stopping_zero_mask_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact prepayment terminal plus strictly earlier Stieltjes dividends
    remains L1 under the true positive-clock mask at an infinite spatial cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hσbound : ∀ ω, σ ω ≤ T) :
    Integrable (fun ω =>
      if σ ω = 0 then w x else
        Real.exp (-(q * (σ ω : ℝ))) *
          w (riskProcess X x D (σ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hTerm : Integrable (fun ω =>
      Real.exp (-(q * (σ ω : ℝ))) *
        w (riskProcess X x D (σ ω) ω)) P :=
    avram_ubv_gauss_top14_original_bounded_stop_prepayment_terminal_L1
      X hX hBV hν q hq w C hC hTop hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x D hD σ hσstop T hσbound
  have hCash : Integrable (fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) P :=
    avram_ubv_gauss13_endpoint_original_bounded_stopped_strict_cash_L1
      X x C D hD q (le_of_lt hq) σ hσstop T hσbound
  exact avram_ubv_loc6_rightcont_stopping_zero_mask_integrable
    σ hσstop _ (hTerm.add hCash) (w x)
