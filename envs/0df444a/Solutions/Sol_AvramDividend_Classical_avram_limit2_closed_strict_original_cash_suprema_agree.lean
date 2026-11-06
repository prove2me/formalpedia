-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_closed_strict_original_cash_suprema_agree
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:57:25.340667+00:00
-- url     : https://prove2.me/submissions/92efec37-0f9f-4e47-b4d8-f267ffe7a8c5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_positive_integer_horizon_exhaustion

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Genuine closed and strictly positive open horizons exhaust the same
    original perpetual discounted Stieltjes cash, retaining every atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D) :
    (⨆ n : ℕ,
      ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) =
    (⨆ n : ℕ,
      ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iio (((n + 1 : ℕ) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) := by
  calc
    _ = dividendValue X q x D :=
      (dividendValue_eq_iSup_truncated X q x D hD).symm
    _ = _ :=
      avram_limit2_original_strict_positive_integer_horizon_exhaustion
        X q x D hD
