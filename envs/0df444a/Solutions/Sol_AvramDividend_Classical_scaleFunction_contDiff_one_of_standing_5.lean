-- Prove2me | solution 5 for AvramDividend.Classical.scaleFunction_contDiff_one_of_standing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T07:41:34.223003+00:00
-- url     : https://prove2.me/submissions/c8d626bb-0079-47be-a30d-0c4fb9a3d4a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_standing_levy_regular_cases
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_infinite_variation_without_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Standing C1 via the proved BV/AC and Gaussian branches, leaving exactly
the source-specific pure infinite-small-jump smoothness obligation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  rcases standing_levy_regular_cases X hX with hbv | hregular
  · exact scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
      X hX q hq W hW hbv.1 hbv.2.2
  · rcases hregular with hσ | hvar
    · exact scaleFunction_contDiff_one_of_gaussian X hX q hq W hW hσ
    · exact scaleFunction_contDiff_one_infinite_variation_without_standing
        X q hq W hW hvar
