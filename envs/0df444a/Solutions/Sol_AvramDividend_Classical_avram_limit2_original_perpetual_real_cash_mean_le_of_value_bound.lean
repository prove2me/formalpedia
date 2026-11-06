-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_perpetual_real_cash_mean_le_of_value_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:28:26.243316+00:00
-- url     : https://prove2.me/submissions/118e9159-3840-4ce3-8fda-d9257d5796df

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A finite bound on expected perpetual dividends gives the original real
Stieltjes payout bound and certifies integrability over all payment times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q B : ℝ)
    (hB : 0 ≤ B)
    (hValueBound : dividendValue X q x D ≤ ENNReal.ofReal B) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B := by
  have hFinite : dividendValue X q x D < ⊤ :=
    lt_of_le_of_lt hValueBound ENNReal.ofReal_lt_top
  obtain ⟨hIntegrable, hIdentity⟩ :=
    avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
      X x D hD q hFinite
  refine ⟨hIntegrable, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hB).mp
  simpa only [hIdentity] using hValueBound
