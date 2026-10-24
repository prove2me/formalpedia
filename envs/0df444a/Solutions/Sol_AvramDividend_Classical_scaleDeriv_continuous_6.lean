-- Prove2me | solution 6 for AvramDividend.Classical.scaleDeriv_continuous
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:34:53.666289+00:00
-- url     : https://prove2.me/submissions/bc822152-4fab-4b37-af60-fa2481732b99
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Continuity of the scale derivative follows from C¹ regularity on the
open positive half-line, using the exact derivative-order inequality.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContinuousOn (deriv W) (Ioi (0 : ℝ)) := by
  have hC1 : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_of_standing X hX q hq W hW
  exact hC1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
