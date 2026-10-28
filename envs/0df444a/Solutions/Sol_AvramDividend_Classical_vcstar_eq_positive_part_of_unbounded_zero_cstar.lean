-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_eq_positive_part_of_unbounded_zero_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:44:37.675011+00:00
-- url     : https://prove2.me/submissions/dc3c5edf-68ae-48b4-b02a-fe6280fabe1e

import Theorems.Thm_AvramDividend_Classical_unbounded_variation_zero_barrier_candidate_eq_posPart
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- At a zero optimal barrier for unbounded variation, the actual vcstar
candidate is exactly the positive part of the reserve globally. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hc0 : cstar W = 0) (x : ℝ) :
    vcstar W x = max x 0 := by
  change barrierValue W (cstar W).toReal x = max x 0
  simpa [hc0] using
    (unbounded_variation_zero_barrier_candidate_eq_posPart
      X q hq W hW hnbv x)
