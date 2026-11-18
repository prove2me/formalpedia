-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB164_original_strict_cash_lower_without_finiteness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:43:22.236215+00:00
-- url     : https://prove2.me/submissions/c61394a4-e188-4e3a-a95e-9ddb8d9b608c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB154_original_gaussian_tube_strict_cash_real_lower_by_dividend_regulator
import Theorems.Thm_AvramDividend_Classical_avram_gbB163_original_equal_cap_barrier_finite_discounted_strict_stopped_cash
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Original Stieltjes cash bound with source-Proved finiteness. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (S T : ℝ≥0) (hST : S < T)
    (hTube : ∀ t : ℝ≥0, t ≤ T →
      |X.X t ω| ≤ (1 / 400 : ℝ))
    (q : ℝ) (hq : 0 ≤ q)
    :
    Real.exp (-(q * (S : ℝ))) *
      barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ) S ω ≤
    (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩
        Iio (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)).toReal := by
  have hFin := avram_gbB163_original_equal_cap_barrier_finite_discounted_strict_stopped_cash
    X ω T q hq
  exact avram_gbB154_original_gaussian_tube_strict_cash_real_lower_by_dividend_regulator
    X ω S T hST hTube q hq hFin
