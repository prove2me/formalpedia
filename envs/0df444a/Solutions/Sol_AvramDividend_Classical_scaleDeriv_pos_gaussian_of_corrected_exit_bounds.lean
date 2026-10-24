-- Prove2me | solution 1 for AvramDividend.Classical.scaleDeriv_pos_gaussian_of_corrected_exit_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:57:59.380125+00:00
-- url     : https://prove2.me/submissions/c0d46900-f2be-4688-a97c-1e240d06f214

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_corrected_exit_bound_gaussian_tilted
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_gaussian_tilt
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Gaussian strict scale-slope positivity from corrected exit inequalities. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a))
    (hBound : ∀ φ : ℝ, 0 < φ → X.ψ φ = q →
      ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
        twoSidedExitExpectationCorrected X q a x ≤
          ENNReal.ofReal (Real.exp (-φ * (a - x)))) :
    ∀ x : ℝ, 0 < x → 0 < deriv W x := by
  obtain ⟨φ, hφ, _, hmono⟩ :=
    corrected_exit_bound_gaussian_tilted X q hq W hW hσ hExit hBound
  have hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_of_gaussian X hX q hq W hW hσ
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact (hreg.differentiableOn_one x hx).differentiableAt
      (isOpen_Ioi.mem_nhds hx)
  exact scaleDeriv_pos_of_gaussian_tilt X q W hW hσ φ hφ hmono hdiff
