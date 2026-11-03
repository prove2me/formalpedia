-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_positive_discount_unrestricted_signed_L1_mean_budget_to_ennreal_value_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:56:41.968285+00:00
-- url     : https://prove2.me/submissions/efc23d28-8806-4c33-80ff-b2a8c792f820

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_positive_discount_dividendValue_finite_iff_genuine_unrestricted_signed_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- A true L1 bounded expectation of unrestricted original signed
    dividend Stieltjes cash bounds canonical ENNReal dividendValue when
    q>0; admissibility supplies the necessary pathwise finiteness. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (hRealIntegrable : Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P)
    (B : ℝ)
    (hRealBudget : (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    dividendValue X q x D ≤ ENNReal.ofReal B := by
  have hFinite : dividendValue X q x D < ⊤ :=
    (avram_wave7_03_positive_discount_dividendValue_finite_iff_genuine_unrestricted_signed_L1
      X x C D hD q hq).2 hRealIntegrable
  have hMeanEq :=
    (avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
      X x D hD.1.1 q hFinite).2
  calc
    dividendValue X q x D =
        ENNReal.ofReal
          (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := hMeanEq
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hRealBudget
