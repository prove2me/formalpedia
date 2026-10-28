-- Prove2me | solution 5 for AvramDividend.Classical.zero_cap_boundary_value_package
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T06:20:20.731743+00:00
-- url     : https://prove2.me/submissions/7d93a534-d467-41e2-a7ff-94a6dc79f01b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_boundary_nonneg
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound_of_boundary
import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The zero-cap boundary package follows directly from the stochastic
comparison and the remaining zero-barrier value identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    0 ≤ barrierValue W 0 0 ∧
      valueFunctionLe X q 0 0 ≤ ENNReal.ofReal (barrierValue W 0 0) := by
  refine ⟨barrierValue_zero_boundary_nonneg X hX q hq W hW, ?_⟩
  exact zero_cap_value_at_zero_upper_bound_of_boundary
    X hX q hq W (barrier_zero_boundary_value X hX q hq W hW)
