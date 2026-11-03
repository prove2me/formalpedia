-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_lower_discount_finite_implies_ae_full_signed_L1_higher_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:39:03.338883+00:00
-- url     : https://prove2.me/submissions/e2e611c6-abc1-4c4d-9933-0e4baac3c059

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_dividendValue_antitone_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_general_original_value_finite_iff_genuine_signed_L1_and_pathwise_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Finiteness at a lower discount rate guarantees actual signed Stieltjes
    integrability on almost every original pre-ruin path at all higher rates. -/
/- W7-03 fresh source snapshot: exact original-measure proof body preserved. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q₀ q : ℝ) (hq : q₀ ≤ q)
    (hFinite : dividendValue X q₀ x D < ⊤) :
    ∀ᵐ ω ∂P,
      IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
        (paymentTimes (ruinTime X x D ω)) (dividendMeasure D ω) := by
  have hFiniteQ : dividendValue X q x D < ⊤ :=
    lt_of_le_of_lt
      (avram_wave7_03_original_dividendValue_antitone_discount
        X x D q₀ q hq) hFinite
  have hAeCash : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) < ⊤ :=
    ((avram_wave7_03_general_original_value_finite_iff_genuine_signed_L1_and_pathwise_finite
      X x D hD q).mp hFiniteQ).2
  filter_upwards [hAeCash] with ω hCash
  exact
    ((avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
      X x D hD ω q).mp hCash)
