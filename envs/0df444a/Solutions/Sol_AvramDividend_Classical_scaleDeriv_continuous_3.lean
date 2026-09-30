-- Prove2me | solution 3 for AvramDividend.Classical.scaleDeriv_continuous
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T06:32:35.183965+00:00
-- url     : https://prove2.me/submissions/cf6be96e-1896-46bf-ad51-84df166f7fa3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContinuousOn (deriv W) (Ioi 0) := by
  have hreg : ContDiffOn ℝ 1 W (Ioi 0) :=
    scaleFunction_contDiff_one X hX q hq W hW
  exact hreg.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)
