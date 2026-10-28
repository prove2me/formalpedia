-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_global_C2_gaussian_of_positive_tilt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T08:27:47.496055+00:00
-- url     : https://prove2.me/submissions/3212aec2-56af-42a9-a85f-29340fdc5800

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous_of_gaussian
import Theorems.Thm_AvramDividend_Classical_deriv_deriv_eq_zero_at_positive_cstar_of_deriv_continuous
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_gaussian_tilt
import Theorems.Thm_AvramDividend_Classical_vcstar_C1_of_scale_C1_tilt
import Theorems.Thm_AvramDividend_Classical_vcstar_global_C2_of_C2_scale_stationary_positive_C1
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Gaussian barrier C2 smooth fit follows from positive tilted-scale monotonicity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hcpos : 0 < (cstar W).toReal) (hσ : 0 < X.σ)
    (htilt : ∃ φ : ℝ, 0 < φ ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0)) :
    ContDiffOn ℝ 2 (vcstar W) (Ioi (0 : ℝ)) := by
  have hW2 : ContDiffOn ℝ 2 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_two_of_gaussian X hX q hq W hW hσ
  have hW1 : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_of_gaussian X hX q hq W hW hσ
  have hvc1 : ContDiffOn ℝ 1 (vcstar W) (Ioi (0 : ℝ)) :=
    vcstar_C1_of_scale_C1_tilt X hX q hq W hW hcpos hW1 htilt
  obtain ⟨φ, hφ, hmono⟩ := htilt
  have hWdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact (hW1.differentiableOn_one x hx).differentiableAt
      (Ioi_mem_nhds hx)
  have hpos : 0 < deriv W (cstar W).toReal :=
    scaleDeriv_pos_of_gaussian_tilt X q W hW hσ φ hφ hmono
      hWdiff (cstar W).toReal hcpos
  have hcont : ContinuousOn (deriv W) (Ioi (0 : ℝ)) :=
    scaleDeriv_continuous_of_gaussian X hσ q hq W hW
  have hflat : deriv (deriv W) (cstar W).toReal = 0 :=
    deriv_deriv_eq_zero_at_positive_cstar_of_deriv_continuous
      W hcont hcpos
  exact vcstar_global_C2_of_C2_scale_stationary_positive_C1
    W hcpos hW2 hpos hflat hvc1
