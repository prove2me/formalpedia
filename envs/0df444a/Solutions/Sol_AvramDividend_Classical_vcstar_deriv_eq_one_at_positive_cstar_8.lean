-- Prove2me | solution 8 for AvramDividend.Classical.vcstar_deriv_eq_one_at_positive_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:57:58.242093+00:00
-- url     : https://prove2.me/submissions/1e714967-47c1-44f7-9117-bb043c2959d7

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
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_contDiffOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Exact smooth-fit theorem reduced to corrected killed exit and BV scale C1.
Those two imported obligations remain Open and must be proved to close this. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    deriv (vcstar W) (cstar W).toReal = 1 := by
  have hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a) := by
    intro a x ha hx hxa
    exact two_sided_exit_before_ruin_identity_corrected
      X hX q hq W hW a x ha (le_of_lt hx) hxa
  rcases h_smooth with hσ | hbv | hsmooth
  · exact vcstar_gaussian_smoothfit_of_corrected_exit_identity
      X hX q hq W hW hc hcpos hσ hExit
  · have hac : X.ν ≪ volume :=
      standing_bv_levy_absolutely_continuous X hX hbv
    have hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
      scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
        X hX q hq W hW hbv hac
    exact vcstar_deriv_one_of_bv_contDiff_one
      X hX q hq W hW hc hcpos hbv hreg
  · exact vcstar_deriv_one_of_contDiffOn W hc hcpos hsmooth
