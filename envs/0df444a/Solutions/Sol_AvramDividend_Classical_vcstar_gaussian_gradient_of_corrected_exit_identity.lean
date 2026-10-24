-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_gaussian_gradient_of_corrected_exit_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:54:47.404775+00:00
-- url     : https://prove2.me/submissions/0543321b-0366-4e82-aab7-ea76026627d0

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_gaussian_tilt_monotone_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_gaussian
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_scale_C1_tilt

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Global Gaussian barrier derivative bound from a corrected exit identity.
The C1 scale theorem and the tilt comparison are independently proved. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    ∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ (vcstar W) x ∧ 1 ≤ deriv (vcstar W) x := by
  have hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_of_gaussian X hX q hq W hW hσ
  obtain ⟨φ, hφ, _, hmono⟩ :=
    gaussian_tilt_monotone_of_corrected_exit_identity
      X q hq W hW hσ hExit
  exact vcstar_deriv_ge_one_of_scale_C1_tilt
    X hX q hq W hW hreg ⟨φ, hφ, hmono⟩
