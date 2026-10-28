-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_vcstar_C1_gradient_smoothfit_of_corrected_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:03:09.097996+00:00
-- url     : https://prove2.me/submissions/b81b249f-29fa-44d1-a2d2-5be932e33232

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_gaussian_tilt_monotone_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_vcstar_C1_of_scale_C1_tilt
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_scale_C1_tilt
import Theorems.Thm_AvramDividend_Classical_vcstar_gaussian_smoothfit_of_corrected_exit_identity
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hσ : 0 < X.σ)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    ContDiffOn ℝ 1 (vcstar W) (Ioi (0 : ℝ)) ∧
    (∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ (vcstar W) x ∧
        1 ≤ deriv (vcstar W) x) ∧
    deriv (vcstar W) (cstar W).toReal = 1 := by
  have hC1 : ContDiffOn ℝ 1 W (Ioi 0) :=
    scaleFunction_contDiff_one_gaussian_without_standing
      X q hq W hW hσ
  obtain ⟨φ, hφ, hroot, htilt⟩ :=
    gaussian_tilt_monotone_of_corrected_exit_identity
      X q hq W hW hσ hExit
  have hTilt : ∃ t : ℝ, 0 < t ∧
      MonotoneOn (fun x : ℝ => Real.exp (-t * x) * W x) (Ioi 0) :=
    ⟨φ, hφ, htilt⟩
  have hcpos' : 0 < (cstar W).toReal := ENNReal.toReal_pos hcpos.ne' hc.ne
  refine ⟨?_, ?_, ?_⟩
  · exact vcstar_C1_of_scale_C1_tilt
      X hX q hq W hW hcpos' hC1 hTilt
  · exact vcstar_deriv_ge_one_of_scale_C1_tilt
      X hX q hq W hW hC1 hTilt
  · exact vcstar_gaussian_smoothfit_of_corrected_exit_identity
      X hX q hq W hW hc hcpos hσ hExit
