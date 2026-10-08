-- Prove2me | solution 1 for AvramDividend.Classical.levyMeasure_absolutelyContinuous_of_standing_boundedVariation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T10:08:36.761274+00:00
-- url     : https://prove2.me/submissions/603c3768-bbee-4494-a64d-cfdfc86f0d02

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing)
    (hbv : X.BoundedVariation) :
    X.ν ≪ volume := by
  rcases hX.2.2 with hσ | hvar | hac
  · rw [hbv.1] at hσ
    exact (lt_irrefl 0 hσ).elim
  · exact (ne_of_lt hbv.2 hvar).elim
  · exact hac
