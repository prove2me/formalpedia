-- Prove2me | solution 9 for AvramDividend.Classical.vcstar_deriv_eq_one_at_positive_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:40:07.488296+00:00
-- url     : https://prove2.me/submissions/7cf4b6ff-fd62-4d9c-b670-35d857f9bb74

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_identity_corrected
import Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_continuous_renewal_density_representation
import Theorems.Thm_AvramDividend_Classical_standing_bv_levy_absolutely_continuous
import Theorems.Thm_AvramDividend_Classical_vcstar_gaussian_smoothfit_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_vcstar_bv_smoothfit_of_esscher_integrated_continuous_density
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_contDiffOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- Exact three-way positive-barrier smooth fit reduces directly to two
true frontier leaves: killed exit and continuous BV Esscher renewal density. -/
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
    obtain ⟨φ, c, f, _hφ, _hroot, hcont, hint, hrepr⟩ :=
      bv_ac_esscher_continuous_renewal_density_representation
        X hX q hq W hW hbv hac
    exact vcstar_bv_smoothfit_of_esscher_integrated_continuous_density
      X hX q hq W f hW hc hcpos hbv φ c hcont hint hrepr
  · exact vcstar_deriv_one_of_contDiffOn W hc hcpos hsmooth
