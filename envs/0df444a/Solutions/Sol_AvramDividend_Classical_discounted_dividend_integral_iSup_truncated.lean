-- Prove2me | solution 1 for AvramDividend.Classical.discounted_dividend_integral_iSup_truncated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:39:58.201768+00:00
-- url     : https://prove2.me/submissions/b5a2648b-0396-4cf1-b650-d2d2ab47b1c5

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_lintegral_exhausted_by_natural_horizons

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    ⨆ n : ℕ, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  have hf : Measurable (fun t : ℝ =>
      ENNReal.ofReal (Real.exp (-(q * t)))) := by
    fun_prop
  exact lintegral_exhausted_by_natural_horizons
    (dividendMeasure D ω)
    (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t)))) hf
    (paymentTimes (ruinTime X x D ω))
    (paymentTimes_measurable (ruinTime X x D ω))
