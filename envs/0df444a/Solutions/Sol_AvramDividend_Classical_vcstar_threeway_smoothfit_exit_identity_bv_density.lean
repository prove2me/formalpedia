-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_threeway_smoothfit_exit_identity_bv_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:42:18.940998+00:00
-- url     : https://prove2.me/submissions/2708fb08-97d7-400c-b21a-44d973478a7d

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_corrected_exit_exp_bound_at_positive_root
import Theorems.Thm_AvramDividend_Classical_vcstar_full_smoothfit_of_corrected_exit_and_bv_renewal_density
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- Full three-way smooth fit with two genuine missing packages: corrected
two-sided exit identity and continuous BV Esscher-renewal density. -/
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
  have hBound : ∀ φ : ℝ, 0 < φ → X.ψ φ = q →
      ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
        twoSidedExitExpectationCorrected X q a x ≤
          ENNReal.ofReal (Real.exp (-φ * (a - x))) := by
    intro φ hφ hroot a x ha hx hxa
    simpa only [neg_mul] using
      (corrected_exit_exp_bound_at_positive_root
        X q hq φ hφ hroot a x ha (le_of_lt hx) hxa)
  exact vcstar_full_smoothfit_of_corrected_exit_and_bv_renewal_density
    X hX q hq W hW hc hcpos hExit hBound hBVRep h_smooth
