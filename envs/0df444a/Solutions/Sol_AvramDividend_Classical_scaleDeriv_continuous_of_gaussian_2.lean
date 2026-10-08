-- Prove2me | solution 2 for AvramDividend.Classical.scaleDeriv_continuous_of_gaussian
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:30:56.914098+00:00
-- url     : https://prove2.me/submissions/5d6d8d61-58f9-4503-b09a-19e14e78dcd9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_gaussian_without_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContinuousOn (deriv W) (Ioi 0) := by
  have hC1 : ContDiffOn ℝ 1 W (Ioi 0) :=
    scaleFunction_contDiff_one_gaussian_without_standing X q hq W hW hσ
  exact hC1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
