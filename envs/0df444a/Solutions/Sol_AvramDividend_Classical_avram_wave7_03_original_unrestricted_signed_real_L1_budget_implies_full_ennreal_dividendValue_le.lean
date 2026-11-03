-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_unrestricted_signed_real_L1_budget_implies_full_ennreal_dividendValue_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:55:28.777435+00:00
-- url     : https://prove2.me/submissions/f773ba6d-db9f-48a8-9c23-2d35fcada7ce

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_general_original_value_finite_iff_genuine_signed_L1_and_pathwise_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- A genuinely integrable original unrestricted signed Stieltjes
    expected real budget controls the complete source ENNReal dividendValue
    with the necessary a.e. pathwise finiteness hypothesis explicit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (hAeFinite : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) < ⊤)
    (hRealIntegrable : Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P)
    (B : ℝ)
    (hRealBudget : (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    dividendValue X q x D ≤ ENNReal.ofReal B := by
  have hFinite : dividendValue X q x D < ⊤ :=
    (avram_wave7_03_general_original_value_finite_iff_genuine_signed_L1_and_pathwise_finite
      X x D hD q).2 ⟨hRealIntegrable, hAeFinite⟩
  have hEq :=
    (avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
      X x D hD q hFinite).2
  calc
    dividendValue X q x D =
        ENNReal.ofReal
          (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := hEq
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hRealBudget
