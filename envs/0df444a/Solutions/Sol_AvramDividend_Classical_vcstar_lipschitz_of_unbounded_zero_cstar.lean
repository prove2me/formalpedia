-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_lipschitz_of_unbounded_zero_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:51:52.664885+00:00
-- url     : https://prove2.me/submissions/4eee5069-be77-409c-a04b-218fe0418b88

import Theorems.Thm_AvramDividend_Classical_unbounded_variation_zero_barrier_candidate_lipschitz
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.EMetricSpace.Lipschitz

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The mission's optimal candidate inherits a global unit Lipschitz
estimate when unbounded variation forces a zero optimal barrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hc0 : cstar W = 0) :
    LipschitzWith (1 : ℝ≥0) (vcstar W) := by
  change LipschitzWith (1 : ℝ≥0) (barrierValue W (cstar W).toReal)
  simpa [hc0] using
    (unbounded_variation_zero_barrier_candidate_lipschitz
      X q hq W hW hnbv)
