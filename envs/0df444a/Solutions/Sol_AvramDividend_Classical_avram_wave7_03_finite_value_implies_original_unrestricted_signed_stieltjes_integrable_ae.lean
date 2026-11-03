-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_finite_value_implies_original_unrestricted_signed_stieltjes_integrable_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:34:15.132601+00:00
-- url     : https://prove2.me/submissions/b904c2b1-72e8-45b2-b113-55e8c54087ab

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Finite original expected total dividends force almost-sure integrability
    and exact same-measure ENNReal equality for unrestricted real Stieltjes cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (hFinite : dividendValue X q x D < ⊤) :
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
  let F : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hFm : Measurable F :=
    avram_wave6_08_original_perpetual_stieltjes_cash_measurable
      X x D hD q
  have hValueLin : (∫⁻ ω, F ω ∂P) < ⊤ := by
    simpa only [dividendValue, F] using hFinite
  have hAeFin : ∀ᵐ ω ∂P, F ω < ⊤ :=
    ae_lt_top hFm (ne_of_lt hValueLin)
  filter_upwards [hAeFin] with ω hω
  exact avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
    X x D hD ω q hω
