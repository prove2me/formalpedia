-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_full_smoothfit_of_corrected_exit_and_bv_renewal_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:28:42.843596+00:00
-- url     : https://prove2.me/submissions/fc53d501-4168-4ec9-ab66-69d5d6fbf66e

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_vcstar_gaussian_smoothfit_of_corrected_exit_bounds
import Theorems.Thm_AvramDividend_Classical_scale_C1_of_esscher_integrated_continuous_density
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_bv_contDiff_one
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_contDiffOn
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- All three smooth-fit cases, conditional on the independent Gaussian exit
identity/bound and the BV continuous renewal-density representation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a))
    (hBound : ∀ φ : ℝ, 0 < φ → X.ψ φ = q →
      ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
        twoSidedExitExpectationCorrected X q a x ≤
          ENNReal.ofReal (Real.exp (-φ * (a - x))))
    (hBVRep : X.BoundedVariation →
      ∃ (φ c : ℝ) (f : ℝ → ℝ),
        ContinuousOn f (Ioi (0 : ℝ)) ∧
        (∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x) ∧
        (∀ x : ℝ, 0 < x →
          Real.exp (-(φ * x)) * W x =
            c + ∫ y in (0 : ℝ)..x, f y))
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    deriv (vcstar W) (cstar W).toReal = 1 := by
  rcases h_smooth with hσ | hbv | hC2
  · exact vcstar_gaussian_smoothfit_of_corrected_exit_bounds
      X hX q hq W hW hc hcpos hσ hExit hBound
  · obtain ⟨φ, c, f, hcont, hint, hrepr⟩ := hBVRep hbv
    have hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
      scale_C1_of_esscher_integrated_continuous_density
        W f φ c hcont hint hrepr
    exact vcstar_deriv_one_of_bv_contDiff_one
      X hX q hq W hW hc hcpos hbv hreg
  · exact vcstar_deriv_one_of_contDiffOn W hc hcpos hC2
