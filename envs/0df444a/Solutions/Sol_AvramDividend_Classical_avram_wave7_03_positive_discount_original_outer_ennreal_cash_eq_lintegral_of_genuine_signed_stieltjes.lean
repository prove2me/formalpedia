-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_positive_discount_original_outer_ennreal_cash_eq_lintegral_of_genuine_signed_stieltjes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:51:44.889751+00:00
-- url     : https://prove2.me/submissions/6fa3eced-17fe-4af9-aa29-346fb6e4497d

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
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

/-- At positive discount the canonical double ENNReal source dividends
    equal the outer lintegral of actual unrestricted signed Stieltjes cash,
    even when the expected dividendValue itself is infinite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) :
    dividendValue X q x D =
      (∫⁻ ω : Ω, ENNReal.ofReal
        (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  let F : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  let g : Ω → ℝ := fun ω =>
    ∫ t in paymentTimes (ruinTime X x D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)
  have hAeFin : ∀ᵐ ω ∂P, F ω < ⊤ :=
    avram_wave6_08_original_positive_discount_perpetual_cash_ae_finite_no_standing
      X x C D hD q hq
  change (∫⁻ ω, F ω ∂P) = ∫⁻ ω, ENNReal.ofReal (g ω) ∂P
  apply lintegral_congr_ae
  filter_upwards [hAeFin] with ω hω
  exact (avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
    X x D hD.1.1 ω q hω).2.symm
