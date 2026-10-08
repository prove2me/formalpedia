-- Prove2me | solution 2 for AvramDividend.Classical.scaleFunction_contDiff_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:09:23.031646+00:00
-- url     : https://prove2.me/submissions/5503d87e-4228-4425-be8c-8dbfe3edac71
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_excursion_tail_derivative_representation
import Theorems.Thm_AvramDividend_Classical_continuousOn_measureReal_Ici_of_finite_pos_noAtoms
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_differentiable_continuous_deriv_Ioi

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The C1 theorem reduces directly to the precise Esscher excursion
derivative identity, without three different external C1 branches. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  obtain ⟨φ, μ, hφ, hnull, hfin, hdiff, hrepr⟩ :=
    scaleFunction_excursion_tail_derivative_representation
      X hX q hq W hW
  letI : NullSingletonClass μ := hnull
  have htail :
      ContinuousOn (fun x : ℝ => μ.real (Ici x)) (Ioi 0) :=
    continuousOn_measureReal_Ici_of_finite_pos_noAtoms μ hfin
  have hsum :
      ContinuousOn (fun x : ℝ => φ + μ.real (Ici x)) (Ioi 0) :=
    continuousOn_const.add htail
  have hWcont : ContinuousOn W (Ioi 0) :=
    hW.2.2.1.mono (by
      intro x hx
      change (0 : ℝ) < x at hx
      exact hx.le)
  have hprod :
      ContinuousOn (fun x : ℝ => W x * (φ + μ.real (Ici x))) (Ioi 0) :=
    hWcont.mul hsum
  have hderivCont : ContinuousOn (deriv W) (Ioi 0) :=
    hprod.congr (by
      intro x hx
      exact hrepr x hx)
  have hWdiff : DifferentiableOn ℝ W (Ioi 0) := by
    intro x hx
    exact (hdiff x hx).differentiableWithinAt
  exact contDiffOn_one_of_differentiable_continuous_deriv_Ioi
    W hWdiff hderivCont
