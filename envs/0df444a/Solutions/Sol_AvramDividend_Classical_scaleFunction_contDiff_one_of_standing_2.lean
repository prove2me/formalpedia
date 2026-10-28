-- Prove2me | solution 2 for AvramDividend.Classical.scaleFunction_contDiff_one_of_standing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T15:16:29.823367+00:00
-- url     : https://prove2.me/submissions/bb82e854-3427-48f7-8702-ff4cd7bbeb77
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Recover Standing C1 from the valid bounded-variation AC and
    unbounded-variation cases, avoiding the disproved no-Standing BV claim. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  rcases hX.2.2 with hσ | hvar | hac
  · exact scaleFunction_contDiff_one_gaussian_without_standing X q hq W hW hσ
  · have hnbv : ¬ X.BoundedVariation := by
      intro hbv
      exact (ne_of_lt hbv.2) hvar
    exact scaleFunction_contDiff_one_of_unbounded_variation X q W hW hnbv
  · by_cases hbv : X.BoundedVariation
    · exact scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
        X hX q hq W hW hbv hac
    · exact scaleFunction_contDiff_one_of_unbounded_variation X q W hW hbv
