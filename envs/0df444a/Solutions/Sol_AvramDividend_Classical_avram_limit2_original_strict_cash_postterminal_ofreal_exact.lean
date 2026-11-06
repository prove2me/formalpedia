-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_strict_cash_postterminal_ofreal_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:01:39.996925+00:00
-- url     : https://prove2.me/submissions/17fadb35-0c8f-480a-8ce3-0950dfdfb6a3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Exact original strict stopped cash and nonnegative real terminal
    conversion, requiring the actual cash integral to be finite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (Term : ℝ) (hTerm : 0 ≤ Term)
    (hCashFinite : (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) ≠ ⊤) :
    ENNReal.ofReal ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal + Term) =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) + ENNReal.ofReal Term := by
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hTerm]
  rw [ENNReal.ofReal_toReal hCashFinite]
