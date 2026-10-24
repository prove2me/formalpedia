-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_gaussian_smoothfit_of_corrected_exit_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:35:59.544818+00:00
-- url     : https://prove2.me/submissions/204d45de-e83a-45df-9400-24935d3c2c80

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_corrected_exit_exp_bound_at_positive_root
import Theorems.Thm_AvramDividend_Classical_vcstar_gaussian_smoothfit_of_corrected_exit_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The existing corrected-exit exponential bound removes a redundant
Gaussian smooth-fit assumption: only the corrected exit identity remains. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hσ : 0 < X.σ)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    deriv (vcstar W) (cstar W).toReal = 1 := by
  have hBound : ∀ φ : ℝ, 0 < φ → X.ψ φ = q →
      ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
        twoSidedExitExpectationCorrected X q a x ≤
          ENNReal.ofReal (Real.exp (-φ * (a - x))) := by
    intro φ hφ hroot a x ha hx hxa
    simpa only [neg_mul] using
      (corrected_exit_exp_bound_at_positive_root
        X q hq φ hφ hroot a x ha (le_of_lt hx) hxa)
  exact vcstar_gaussian_smoothfit_of_corrected_exit_bounds
    X hX q hq W hW hc hcpos hσ hExit hBound
