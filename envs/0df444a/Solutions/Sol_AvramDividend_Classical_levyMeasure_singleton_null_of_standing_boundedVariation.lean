-- Prove2me | solution 1 for AvramDividend.Classical.levyMeasure_singleton_null_of_standing_boundedVariation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:23:09.444434+00:00
-- url     : https://prove2.me/submissions/695dc7a0-2ecb-422e-b2b1-f718daebe14c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levyMeasure_absolutelyContinuous_of_standing_boundedVariation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (y : ℝ) :
    X.ν {y} = 0 := by
  have hac : X.ν ≪ volume :=
    levyMeasure_absolutelyContinuous_of_standing_boundedVariation
      X hX hbv
  exact hac (measure_singleton y)
