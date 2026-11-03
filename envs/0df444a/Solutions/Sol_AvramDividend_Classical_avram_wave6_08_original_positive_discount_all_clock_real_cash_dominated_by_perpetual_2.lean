-- Prove2me | solution 2 for AvramDividend.Classical.avram_wave6_08_original_positive_discount_all_clock_real_cash_dominated_by_perpetual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:45:29.011066+00:00
-- url     : https://prove2.me/submissions/782b3b63-bf69-416a-bb72-d84fc1fb3d08

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_discount_perpetual_cash_ae_finite_no_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

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
  filter_upwards [
    avram_wave6_08_original_positive_discount_perpetual_cash_ae_finite_no_standing
      X x C D hD q hq] with ω hfin T
  apply ENNReal.toReal_mono (ne_of_lt hfin)
  exact lintegral_mono_set (Set.inter_subset_left)
