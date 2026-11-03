-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_positive_discount_all_clock_real_cash_dominated_by_perpetual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:44:29.189992+00:00
-- url     : https://prove2.me/submissions/8e9259ca-f447-4b8f-906c-c9e7c56691db

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_discount_perpetual_cash_ae_finite_no_standing
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) :
    ∀ᵐ ω ∂P, ∀ T : ℝ,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal := by
  filter_upwards [avram_wave6_08_original_positive_discount_perpetual_cash_ae_finite_no_standing
    X x C D hD q hq] with ω hfinite
  intro T
  apply ENNReal.toReal_mono (ne_of_lt hfinite)
  apply lintegral_mono_set
  intro t ht
  exact ht.1
