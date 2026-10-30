-- Prove2me | solution 9 for AvramDividend.Classical.scaleDeriv_tendsto_atTop
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T07:45:15.613908+00:00
-- url     : https://prove2.me/submissions/8747f7d7-83c8-4f78-95c5-2e73dd01aa97
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_cr_new_standing_bv_derivative_diverges
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_scale_deriv_tendsto_atTop_of_normalized_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- Derivative divergence follows from verified BV growth and unbounded
Esscher monotonicity, conditional only on Standing C1 regularity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Tendsto (deriv W) atTop atTop := by
  by_cases hBV : X.BoundedVariation
  · exact avram_ws01e_cr_new_standing_bv_derivative_diverges
      X hX q hq W hW hBV
  · obtain ⟨hpos, φ, hφ, htilt⟩ :=
      unbounded_tilted_positive_monotone X q hq W hW hBV
    have hreg : ContDiffOn ℝ 1 W (Ioi 0) :=
      scaleFunction_contDiff_one_of_standing X hX q hq W hW
    have hW1 : 0 < W 1 := hpos 1 (by norm_num)
    have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
      intro x hx
      exact (hreg.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioi.mem_nhds hx)
    exact scale_deriv_tendsto_atTop_of_normalized_monotone
      W φ hφ hW1 htilt hdiff
