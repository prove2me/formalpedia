-- Prove2me | solution 9 for AvramDividend.Classical.scaleDeriv_pos
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:10:15.664052+00:00
-- url     : https://prove2.me/submissions/4ec67935-c091-4813-97a2-f73cc5347266
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_deriv_pos_of_pointwise_diff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

/-- The canonical global positive derivative statement follows from
the only unresolved Standing C1 scale theorem and accepted local positivity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 < x → 0 < deriv W x := by
  intro x hx
  have hC1 : ContDiffOn ℝ 1 W (Ioi 0) :=
    scaleFunction_contDiff_one_of_standing X hX q hq W hW
  have hdiffOn : DifferentiableOn ℝ W (Ioi 0) :=
    ContDiffOn.differentiableOn_one hC1
  have hdiff : DifferentiableAt ℝ W x :=
    hdiffOn.differentiableAt
      (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hx))
  exact avram_wave3_02_deriv_pos_of_pointwise_diff
    X hX q hq W hW x hx hdiff
