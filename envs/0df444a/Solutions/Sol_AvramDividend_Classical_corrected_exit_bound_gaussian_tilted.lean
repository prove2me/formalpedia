-- Prove2me | solution 1 for AvramDividend.Classical.corrected_exit_bound_gaussian_tilted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T21:18:32.644988+00:00
-- url     : https://prove2.me/submissions/9db1f8d9-76bc-497f-9838-5bd9a42f78f7

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_gaussian
import Theorems.Thm_AvramDividend_Classical_gaussian_ratio_bound_tilted_monotone
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The corrected killed exit identity and the true exponential exit estimate give a monotone Esscher tilt. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
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
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  have hpos : ∀ x : ℝ, 0 < x → 0 < W x := by
    intro x hx
    exact scaleFunction_strict_pos_of_gaussian X q W hW hσ x hx
  apply gaussian_ratio_bound_tilted_monotone X q hq hσ W hpos
  intro φ hφ hroot x y hx hxy
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hEq := hExit y x hy hx hxy
  have hUpper := hBound φ hφ hroot y x hy hx hxy
  rw [hEq] at hUpper
  exact (ENNReal.ofReal_le_ofReal_iff
    (le_of_lt (Real.exp_pos _))).mp hUpper
