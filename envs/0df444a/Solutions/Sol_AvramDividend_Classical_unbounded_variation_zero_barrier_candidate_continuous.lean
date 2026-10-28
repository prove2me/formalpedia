-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_variation_zero_barrier_candidate_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:32:14.999805+00:00
-- url     : https://prove2.me/submissions/0b2ade23-904d-4aee-97b5-7094accc30bd

import Theorems.Thm_AvramDividend_Classical_unbounded_variation_zero_barrier_candidate_eq_posPart
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Under unbounded variation the zero-barrier dividend candidate is globally
continuous, including across the origin, as the reserve's positive part. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    Continuous (barrierValue W 0) := by
  have heq : barrierValue W 0 = fun x : ℝ => max x 0 := by
    funext x
    exact unbounded_variation_zero_barrier_candidate_eq_posPart
      X q hq W hW hnbv x
  rw [heq]
  exact continuous_id.max continuous_const
