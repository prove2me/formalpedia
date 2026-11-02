-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_original_single_bounded_clock_budget_exact_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:15:24.752281+00:00
-- url     : https://prove2.me/submissions/e79e05e0-bba0-4937-ab71-72c7581bb19a

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_original_zero_endpoint_finite_horizon_payment_domain_clip

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (w : ℝ → ℝ)
    (T : ℝ) (hT : 0 ≤ T)
    (a : ℝ≥0∞) (hTa : ENNReal.ofReal T < a)
    (hBudget :
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) a) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  simpa only [
    avram_wave6_original_zero_endpoint_finite_horizon_payment_domain_clip
      X x C D hD T hT a hTa] using hBudget
end
