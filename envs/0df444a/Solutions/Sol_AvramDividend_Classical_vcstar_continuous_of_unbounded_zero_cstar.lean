-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_continuous_of_unbounded_zero_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:58:22.986881+00:00
-- url     : https://prove2.me/submissions/9f988635-523b-41df-8e15-9a2f1ed329b2

import Theorems.Thm_AvramDividend_Classical_unbounded_variation_zero_barrier_candidate_continuous
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The zero-barrier optimal candidate inherits continuous from its
verified zero-barrier scale-function value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hc0 : cstar W = 0) :
    Continuous (vcstar W) := by
  change Continuous (barrierValue W (cstar W).toReal)
  simpa [hc0] using
    (unbounded_variation_zero_barrier_candidate_continuous X q hq W hW hnbv)
