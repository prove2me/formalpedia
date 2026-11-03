-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_outer_cash_eq_lintegral_genuine_signed_of_ae_pathwise_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:53:29.642446+00:00
-- url     : https://prove2.me/submissions/26170330-2dc3-43b1-8b79-d4205d9918db

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Exact full original outer signed-to-ENNReal Stieltjes equality at
    any discount with precisely the necessary a.e. pathwise finiteness;
    expected dividends themselves may be infinite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (hAeFinite : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) < ⊤) :
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
  change (∫⁻ ω, F ω ∂P) = ∫⁻ ω, ENNReal.ofReal (g ω) ∂P
  apply lintegral_congr_ae
  filter_upwards [hAeFinite] with ω hω
  exact (avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
    X x D hD ω q hω).2.symm
