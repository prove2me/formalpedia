-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_postsource_rightpayment_reserve_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:00:55.5612+00:00
-- url     : https://prove2.me/submissions/4bdee4a4-1bb7-4ee0-970d-a9abc3e9283e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- The original source jump has already occurred before the right dividend is paid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0) :
    x + X.X t ω - rightLimit D t ω =
      riskProcess X x D t ω - (rightLimit D t ω - D t ω) := by
  simp only [riskProcess]
  ring
