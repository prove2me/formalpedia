-- Prove2me | solution 7 for AvramDividend.Classical.scaleDeriv_tendsto_atTop
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:26:41.154393+00:00
-- url     : https://prove2.me/submissions/683e3d5f-1fd7-43db-9e42-e691829c3ebb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_bv_scaleDeriv_tendsto_atTop_of_C1
import Theorems.Thm_AvramDividend_Classical_unbounded_scaleDeriv_growth_of_corrected_exit_and_C1
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_identity_corrected
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- Combine the Proved BV and unbounded-variation derivative-growth
branches using canonical Standing regularity and corrected first passage. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Tendsto (deriv W) atTop atTop := by
  have hC1 : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_of_standing X hX q hq W hW
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact hC1.differentiableOn_one.differentiableAt
      (isOpen_Ioi.mem_nhds hx)
  by_cases hbv : X.BoundedVariation
  · exact bv_scaleDeriv_tendsto_atTop_of_C1 X hX q hq W hW hbv hdiff
  · apply unbounded_scaleDeriv_growth_of_corrected_exit_and_C1
      X q hq W hW hbv ?_ hdiff
    intro a x ha hx hxa
    exact two_sided_exit_before_ruin_identity_corrected
      X hX q hq W hW a x ha hx hxa
