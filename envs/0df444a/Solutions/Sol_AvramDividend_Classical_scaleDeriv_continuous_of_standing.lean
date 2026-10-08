-- Prove2me | solution 1 for AvramDividend.Classical.scaleDeriv_continuous_of_standing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:52:06.08506+00:00
-- url     : https://prove2.me/submissions/b5679806-69d9-43e0-8610-21dd30e95a3e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) :
    ContinuousOn (deriv W) (Ioi 0) := by
  have hC1 : ContDiffOn ℝ 1 W (Ioi 0) :=
    AvramDividend.Classical.scaleFunction_contDiff_one_of_standing X hX q hq W hW
  exact hC1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
