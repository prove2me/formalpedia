-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bf_new_gaussian_or_bv_global_gradient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:00:19.651924+00:00
-- url     : https://prove2.me/submissions/ead8f5e8-5095-46ab-908e-a9bdb2eaab62

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_gaussian
import Theorems.Thm_AvramDividend_Classical_standing_bv_levy_absolutely_continuous
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_scale_C1_tilt
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The Gaussian and BV branches satisfy the global dividend gradient bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hregular : 0 < X.σ ∨ X.BoundedVariation) :
    ∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ (vcstar W) x ∧ 1 ≤ deriv (vcstar W) x := by
  have hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by
    rcases hregular with hgauss | hbv
    · exact scaleFunction_contDiff_one_of_gaussian X hX q hq W hW hgauss
    · exact scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
        X hX q hq W hW hbv
        (standing_bv_levy_absolutely_continuous X hX hbv)
  exact vcstar_deriv_ge_one_of_scale_C1_tilt
    X hX q hq W hW hreg
    (scaleFunction_tilted_positive_monotone X hX q hq W hW).2
