-- Prove2me | solution 2 for AvramDividend.Classical.vcstar_global_C2_gaussian_of_positive_tilt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:28:51.454782+00:00
-- url     : https://prove2.me/submissions/e95b9842-b92c-4aef-97cc-fc3a807fe79a

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
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

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
  have h1 := AvramDividend.Classical.scaleFunction_contDiff_one_of_gaussian X hX q hq W hW hσ
  have hdiff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ W y := fun y hy =>
    ((h1.differentiableOn one_ne_zero) y hy).differentiableAt (Ioi_mem_nhds hy)
  obtain ⟨φ, hφ, hmono⟩ := htilt
  exact AvramDividend.Classical.vcstar_global_C2_of_C2_scale_stationary_positive_C1 W hcpos
    (AvramDividend.Classical.scaleFunction_contDiff_two_of_gaussian X hX q hq W hW hσ)
    (AvramDividend.Classical.scaleDeriv_pos_of_gaussian_tilt X q W hW hσ φ hφ hmono hdiff _ hcpos)
    (AvramDividend.Classical.deriv_deriv_eq_zero_at_positive_cstar_of_deriv_continuous W
      (AvramDividend.Classical.scaleDeriv_continuous_of_gaussian X hσ q hq W hW) hcpos)
    (AvramDividend.Classical.vcstar_C1_of_scale_C1_tilt X hX q hq W hW hcpos h1 ⟨φ, hφ, hmono⟩)
