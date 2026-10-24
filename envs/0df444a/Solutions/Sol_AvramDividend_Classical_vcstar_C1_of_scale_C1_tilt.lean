-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_C1_of_scale_C1_tilt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:34:06.71782+00:00
-- url     : https://prove2.me/submissions/6ef73d6e-2803-47e7-a427-1d591aa45009

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_scale_C1_tilt
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_continuous_C1_positive
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_differentiable_continuous_deriv_Ioi
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Global C1 regularity for the barrier candidate, conditional on C1 scale
smoothness and a positive monotone tilted scale; these conditions are explicit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hcpos : 0 < (cstar W).toReal)
    (hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)))
    (htilt : ∃ φ : ℝ, 0 < φ ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0)) :
    ContDiffOn ℝ 1 (vcstar W) (Ioi (0 : ℝ)) := by
  have hWdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact (hreg.differentiableOn_one x hx).differentiableAt
      (Ioi_mem_nhds hx)
  have hWpos : ∀ x : ℝ, 0 < x → 0 < W x := by
    intro x hx
    exact scaleFunction_strict_pos_of_standing X hX q hq W hW x hx
  have hDpos : 0 < deriv W (cstar W).toReal :=
    scaleDeriv_pos_of_tilted_positive_monotone
      X hX q hq W hW hWpos hWdiff htilt _ hcpos
  have hVdiff : DifferentiableOn ℝ (vcstar W) (Ioi (0 : ℝ)) := by
    intro x hx
    exact ((vcstar_deriv_ge_one_of_scale_C1_tilt
      X hX q hq W hW hreg htilt x hx).1).differentiableWithinAt
  have hVcont : ContinuousOn (deriv (vcstar W)) (Ioi (0 : ℝ)) :=
    vcstar_deriv_continuous_C1_positive W hcpos hreg hDpos
  exact contDiffOn_one_of_differentiable_continuous_deriv_Ioi
    (vcstar W) hVdiff hVcont
