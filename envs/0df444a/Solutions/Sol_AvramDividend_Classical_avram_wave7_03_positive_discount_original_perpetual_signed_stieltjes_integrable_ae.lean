-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_positive_discount_original_perpetual_signed_stieltjes_integrable_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:34:21.545203+00:00
-- url     : https://prove2.me/submissions/d17d7290-6f21-4c74-9b29-6b5a5e82cebb

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_discount_perpetual_cash_ae_finite_no_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Original q>0 discounted perpetual real Stieltjes cash is
    pathwise integrable and exactly ENNReal-convertible P-a.e., without
    requiring finite expected dividends. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) :
    ∀ᵐ ω ∂P,
      IntegrableOn
        (fun t : ℝ => Real.exp (-(q * t)))
        (paymentTimes (ruinTime X x D ω))
        (dividendMeasure D ω) ∧
      ENNReal.ofReal
        (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) =
        (∫⁻ t in paymentTimes (ruinTime X x D ω),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) := by
  filter_upwards [
    avram_wave6_08_original_positive_discount_perpetual_cash_ae_finite_no_standing
      X x C D hD q hq] with ω hω
  exact avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
    X x D hD.1.1 ω q hω
