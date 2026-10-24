-- Prove2me | solution 6 for AvramDividend.Classical.vcstar_differentiableAt_positive_cstar_of_gaussian_or_bv
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:21:54.484909+00:00
-- url     : https://prove2.me/submissions/a769a8f3-f313-4d8c-a551-5120e7128267
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_identity_corrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
import Theorems.Thm_AvramDividend_Classical_standing_bv_levy_absolutely_continuous
import Theorems.Thm_AvramDividend_Classical_vcstar_gaussian_smoothfit_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_bv_contDiff_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Differentiability at the positive optimal barrier reduces to the
corrected killed-exit identity and the BV positive-axis C1 scale theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hregular : 0 < X.σ ∨ X.BoundedVariation) :
    DifferentiableAt ℝ (vcstar W) (cstar W).toReal := by
  have hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a) := by
    intro a x ha hx hxa
    exact two_sided_exit_before_ruin_identity_corrected
      X hX q hq W hW a x ha (le_of_lt hx) hxa
  have hv : deriv (vcstar W) (cstar W).toReal = 1 := by
    rcases hregular with hσ | hbv
    · exact vcstar_gaussian_smoothfit_of_corrected_exit_identity
        X hX q hq W hW hc hcpos hσ hExit
    · have hac : X.ν ≪ volume :=
        standing_bv_levy_absolutely_continuous X hX hbv
      have hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
        scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
          X hX q hq W hW hbv hac
      exact vcstar_deriv_one_of_bv_contDiff_one
        X hX q hq W hW hc hcpos hbv hreg
  have hvne : deriv (vcstar W) (cstar W).toReal ≠ 0 := by
    rw [hv]
    exact one_ne_zero
  exact differentiableAt_of_deriv_ne_zero hvne
