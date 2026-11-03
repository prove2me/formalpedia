-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_finite_original_value_implies_ae_higher_discount_genuine_signed_integrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:05:36.367597+00:00
-- url     : https://prove2.me/submissions/fe735b33-b5b5-4d8a-944d-cf755a79d9d3

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_dividendValue_antitone_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_general_original_value_finite_iff_genuine_signed_L1_and_pathwise_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Finite original dividend value at one discount implies genuine signed
    Stieltjes integrability at every larger discount on almost every path. -/
/- Fresh proof snapshot following earlier terminal storage rejection. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q₁ q₂ : ℝ) (hq : q₁ ≤ q₂)
    (hFinite : dividendValue X q₁ x D < ⊤) :
    ∀ᵐ ω ∂P, IntegrableOn
      (fun t : ℝ => Real.exp (-(q₂ * t)))
      (paymentTimes (ruinTime X x D ω))
      (dividendMeasure D ω) := by
  have hFinite₂ : dividendValue X q₂ x D < ⊤ :=
    lt_of_le_of_lt
      (avram_wave7_03_original_dividendValue_antitone_discount
        X x D q₁ q₂ hq) hFinite
  have hAeCash : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q₂ * t)))
          ∂(dividendMeasure D ω)) < ⊤ :=
    ((avram_wave7_03_general_original_value_finite_iff_genuine_signed_L1_and_pathwise_finite
      X x D hD q₂).mp hFinite₂).2
  filter_upwards [hAeCash] with ω hω
  exact
    (avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
      X x D hD ω q₂).mp hω
