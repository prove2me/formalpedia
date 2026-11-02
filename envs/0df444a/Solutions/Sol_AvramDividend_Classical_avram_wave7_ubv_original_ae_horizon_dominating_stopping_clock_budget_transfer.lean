-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_ubv_original_ae_horizon_dominating_stopping_clock_budget_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:20:17.93049+00:00
-- url     : https://prove2.me/submissions/bf6f82df-a1a9-4ac1-89c5-b9113fd796a9

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_original_zero_endpoint_finite_horizon_payment_domain_clip

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Transfer a full discounted dividend budget from one genuine original
    stopping clock exceeding the observation horizon almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (w : ℝ → ℝ)
    (T : ℝ) (hT : 0 ≤ T)
    (S : Ω → ℝ≥0∞)
    (hSstop : IsStoppingTime 𝓕.rightCont S)
    (hSbigAE : ∀ᵐ ω ∂P, ENNReal.ofReal T < S ω)
    (hBudget :
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (S ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (S ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
          apply lintegral_congr_ae
          filter_upwards [hSbigAE] with ω hω
          rw [avram_wave6_original_zero_endpoint_finite_horizon_payment_domain_clip
            X x C D hD T hT (S ω) hω ω]
    _ ≤ ENNReal.ofReal (w x) := hBudget
end
