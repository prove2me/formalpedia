-- Prove2me | solution 3 for AvramDividend.Classical.zero_cap_value_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:19:36.530228+00:00
-- url     : https://prove2.me/submissions/bee6fd9f-a47a-465e-9b7c-5c62e0470a8e

import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_of_zero_bound
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_boundary_nonneg
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The global zero-cap upper bound reduces to the value bound at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by
  intro x hx
  exact zero_cap_value_upper_bound_of_zero_bound X q W
    (zero_cap_value_at_zero_upper_bound X hX q hq W hW)
    (barrierValue_zero_boundary_nonneg X hX q hq W hW) x hx
