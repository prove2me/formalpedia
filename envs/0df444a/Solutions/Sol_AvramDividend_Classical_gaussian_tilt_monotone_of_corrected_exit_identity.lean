-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_tilt_monotone_of_corrected_exit_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:36:19.837376+00:00
-- url     : https://prove2.me/submissions/e870d8b6-c4f7-4e1a-8c4d-d382e041a40f

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_corrected_exit_exp_bound_at_positive_root
import Theorems.Thm_AvramDividend_Classical_corrected_exit_bound_gaussian_tilted
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Gaussian Esscher-monotone scale function from the corrected exit identity.
The exponential bound is already an independently Proved stopped estimate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  have hBound : ∀ φ : ℝ, 0 < φ → X.ψ φ = q →
      ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
        twoSidedExitExpectationCorrected X q a x ≤
          ENNReal.ofReal (Real.exp (-φ * (a - x))) := by
    intro φ hφ hroot a x ha hx hxa
    simpa only [neg_mul] using
      (corrected_exit_exp_bound_at_positive_root
        X q hq φ hφ hroot a x ha (le_of_lt hx) hxa)
  exact corrected_exit_bound_gaussian_tilted
    X q hq W hW hσ hExit hBound
