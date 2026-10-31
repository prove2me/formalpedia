-- Prove2me | solution 6 for AvramDividend.Classical.scaleFunction_contDiff_one_of_standing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:03:54.760885+00:00
-- url     : https://prove2.me/submissions/c6bd5733-35e5-4542-9302-2ec6a451a9be
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_standing_levy_regular_cases
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_infinite_variation_without_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Standing C1 at positive discount follows directly by the source Lévy
    regularity trichotomy, without an all-discount C1 theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  rcases standing_levy_regular_cases X hX with
    ⟨hbv, _, hac⟩ | hnbv
  · exact scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
      X hX q hq W hW hbv hac
  · rcases hnbv with hσ | hvar
    · exact scaleFunction_contDiff_one_gaussian_without_standing
        X q hq W hW hσ
    · exact scaleFunction_contDiff_one_infinite_variation_without_standing
        X q hq W hW hvar
