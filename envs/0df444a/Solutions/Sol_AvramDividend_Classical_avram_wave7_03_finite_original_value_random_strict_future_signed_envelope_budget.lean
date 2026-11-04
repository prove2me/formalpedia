-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_finite_original_value_random_strict_future_signed_envelope_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:18:18.622954+00:00
-- url     : https://prove2.me/submissions/b78b3102-30d8-4409-997c-c6ba8c1f29b6

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_value_implies_original_unrestricted_signed_stieltjes_integrable_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_random_strict_future_signed_envelope_to_ennreal_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Finite canonical value and a genuine signed future Stieltjes envelope
    bound the exact original expected ENNReal cash remainder. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (T : Ω → ℝ) (B : Ω → ℝ) (K : ℝ)
    (hFinite : dividendValue X q x D < ⊤)
    (hSignedBound : ∀ᵐ ω ∂P,
      (∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤ B ω)
    (hBInt : Integrable B P)
    (hBMean : (∫ ω, B ω ∂P) ≤ K) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal K := by
  have hFull :=
    avram_wave7_03_finite_value_implies_original_unrestricted_signed_stieltjes_integrable_ae
      X x D hD q hFinite
  have hIntCash : ∀ᵐ ω ∂P,
      IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
        (paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω))
        (dividendMeasure D ω) := by
    filter_upwards [hFull] with ω hω
    exact hω.1.mono inter_subset_left le_rfl
  exact avram_wave7_03_original_random_strict_future_signed_envelope_to_ennreal_budget
    X x D q T B K hIntCash hSignedBound hBInt hBMean
