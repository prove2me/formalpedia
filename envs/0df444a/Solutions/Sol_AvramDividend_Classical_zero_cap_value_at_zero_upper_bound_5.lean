-- Prove2me | solution 5 for AvramDividend.Classical.zero_cap_value_at_zero_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T06:10:02.44088+00:00
-- url     : https://prove2.me/submissions/626f7fca-7518-4680-96c5-44a035d29ab2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound_of_boundary
import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The proved zero-cap stochastic comparison reduces the upper value bound
to the single boundary valuation for reflection at reserve zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    valueFunctionLe X q 0 0 ≤ ENNReal.ofReal (barrierValue W 0 0) := by
  exact zero_cap_value_at_zero_upper_bound_of_boundary
    X hX q hq W (barrier_zero_boundary_value X hX q hq W hW)
