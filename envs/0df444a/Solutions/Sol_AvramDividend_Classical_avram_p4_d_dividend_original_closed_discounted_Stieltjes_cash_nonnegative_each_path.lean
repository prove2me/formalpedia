-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_closed_discounted_Stieltjes_cash_nonnegative_each_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T01:16:21.24758+00:00
-- url     : https://prove2.me/submissions/06bdd256-f15b-4d28-b73e-2084861b7ff1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual original closed discounted Stieltjes cash over the finite
stopped clock is nonnegative, including its time-zero and horizon atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) :
    ∀ ω, 0 ≤ Cash ω := by
  intro ω
  rw [hCash ω]
  exact ENNReal.toReal_nonneg
