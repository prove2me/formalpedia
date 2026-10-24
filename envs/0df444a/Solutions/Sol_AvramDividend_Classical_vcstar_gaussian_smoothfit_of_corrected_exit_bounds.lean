-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_gaussian_smoothfit_of_corrected_exit_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:53:53.798442+00:00
-- url     : https://prove2.me/submissions/c44cc30b-3dbf-4d72-a89c-16f7e88f5d64

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_corrected_exit_bound_gaussian_tilted
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_gaussian_tilt
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Corrected two-sided exit and Esscher bound imply Gaussian smooth fit. -/
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
        ENNReal.ofReal (W x / W a))
    (hBound : ∀ φ : ℝ, 0 < φ → X.ψ φ = q →
      ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
        twoSidedExitExpectationCorrected X q a x ≤
          ENNReal.ofReal (Real.exp (-φ * (a - x)))) :
    deriv (vcstar W) (cstar W).toReal = 1 := by
  obtain ⟨φ, hφ, _, hmono⟩ :=
    corrected_exit_bound_gaussian_tilted X q hq W hW hσ hExit hBound
  exact vcstar_deriv_one_of_gaussian_tilt
    X hX q hq W hW hc hcpos hσ ⟨φ, hφ, hmono⟩
