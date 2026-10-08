-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_contDiff_one_of_absolutely_continuous_levy
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T11:35:51.319091+00:00
-- url     : https://prove2.me/submissions/05d310e6-d020-4386-bbd5-ad06c7db30fa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_variation_gaussian_or_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_infinite_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The absolutely-continuous Condition33 branch reduces to one genuinely
new BV+AC renewal regularity theorem. In the unbounded-variation case,
the canonical variation dichotomy routes to the Gaussian or infinite-jump
regularity branches. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hac : X.ν ≪ volume) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  by_cases hbv : X.BoundedVariation
  · exact scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
      X hX q hq W hW hbv hac
  · rcases unbounded_variation_gaussian_or_infinite_small_jump_moment X hbv with
      hσ | hvar
    · exact scaleFunction_contDiff_one_of_gaussian X hX q hq W hW hσ
    · exact scaleFunction_contDiff_one_of_infinite_variation X hX q hq W hW hvar
