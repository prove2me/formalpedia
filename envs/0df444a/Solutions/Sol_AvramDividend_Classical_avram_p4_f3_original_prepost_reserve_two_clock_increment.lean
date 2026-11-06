-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_prepost_reserve_two_clock_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:42:42.963765+00:00
-- url     : https://prove2.me/submissions/74aa9ab2-ebed-44aa-949f-34008a66a09f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact two-clock reserve increments before and after right-payment correction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (s t : ℝ≥0) (ω : Ω) :
    (riskProcess X x D t ω - riskProcess X x D s ω =
      (X.X t ω - X.X s ω) - (D t ω - D s ω)) ∧
    ((riskProcess X x D t ω - (rightLimit D t ω - D t ω)) -
      (riskProcess X x D s ω - (rightLimit D s ω - D s ω)) =
      (X.X t ω - X.X s ω) -
        (rightLimit D t ω - rightLimit D s ω)) := by
  constructor
  · change (x + X.X t ω - D t ω) -
      (x + X.X s ω - D s ω) = _
    ring
  · change ((x + X.X t ω - D t ω) -
        (rightLimit D t ω - D t ω)) -
      ((x + X.X s ω - D s ω) -
        (rightLimit D s ω - D s ω)) = _
    ring
