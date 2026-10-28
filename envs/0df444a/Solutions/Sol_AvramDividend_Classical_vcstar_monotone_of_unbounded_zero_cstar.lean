-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_monotone_of_unbounded_zero_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:58:25.958916+00:00
-- url     : https://prove2.me/submissions/6ad021ff-a247-4348-ae40-e2c162619de6

import Theorems.Thm_AvramDividend_Classical_unbounded_variation_zero_barrier_candidate_monotone
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Order.Monotone.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The zero-barrier optimal candidate inherits monotone from its
verified zero-barrier scale-function value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hc0 : cstar W = 0) :
    Monotone (vcstar W) := by
  change Monotone (barrierValue W (cstar W).toReal)
  simpa [hc0] using
    (unbounded_variation_zero_barrier_candidate_monotone X q hq W hW hnbv)
