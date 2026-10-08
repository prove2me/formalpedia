-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_contDiff_one_of_condition33
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:47:09.939789+00:00
-- url     : https://prove2.me/submissions/b0118a5b-d25a-4e7d-bc28-2563c61e4dee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_infinite_variation_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_bv_ac_without_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h33 : X.Condition33) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  rcases h33 with hσ | hvar | hac
  · exact AvramDividend.Classical.scaleFunction_contDiff_one_gaussian_without_standing
      X q hq W hW hσ
  · exact AvramDividend.Classical.scaleFunction_contDiff_one_infinite_variation_without_standing
      X q hq W hW hvar
  · by_cases hσ : 0 < X.σ
    · exact AvramDividend.Classical.scaleFunction_contDiff_one_gaussian_without_standing
        X q hq W hW hσ
    · by_cases hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
          ENNReal.ofReal |y| ∂X.ν) = ⊤
      · exact AvramDividend.Classical.scaleFunction_contDiff_one_infinite_variation_without_standing
          X q hq W hW hvar
      · have hbv : X.BoundedVariation := by
          refine ⟨le_antisymm (le_of_not_gt hσ) X.σ_nonneg, ?_⟩
          exact lt_top_iff_ne_top.mpr hvar
        exact AvramDividend.Classical.scaleFunction_contDiff_one_bv_ac_without_standing
          X q hq W hW hbv hac
