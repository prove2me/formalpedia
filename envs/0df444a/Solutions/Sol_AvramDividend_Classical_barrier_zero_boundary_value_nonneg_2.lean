-- Prove2me | solution 2 for AvramDividend.Classical.barrier_zero_boundary_value_nonneg
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:24:38.41114+00:00
-- url     : https://prove2.me/submissions/ae8ff2e3-38de-4917-a014-15cd62d315a1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_value_identity
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_at_nonnegative_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Separate the zero-barrier scale-value positivity from its probabilistic identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    0 ≤ barrierValue W 0 0 ∧
      dividendValue X q 0 (barrierStrategy X 0 0) =
        ENNReal.ofReal (barrierValue W 0 0) := by
  constructor
  · exact barrierValue_nonnegative_at_nonnegative_barrier
      X hX q hq W hW 0 (le_refl 0)
  · exact barrierStrategy_zero_boundary_value_identity X hX q hq W hW
