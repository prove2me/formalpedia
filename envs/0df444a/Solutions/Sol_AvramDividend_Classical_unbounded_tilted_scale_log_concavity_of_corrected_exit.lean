-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_tilted_scale_log_concavity_of_corrected_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:54:03.829993+00:00
-- url     : https://prove2.me/submissions/69a5ab4f-f9c0-4bc5-b8a1-50dfe924846b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_scale_cross_derivative_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_positive_cross_derivative_log_concavity
import Mathlib.Tactic.FunProp
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Global tilted-scale logarithmic concavity follows from corrected exits and C1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a))
    (φ : ℝ)
    (hWdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) :
    ConcaveOn ℝ (Ioi (0 : ℝ))
      (fun z : ℝ => Real.log (Real.exp (-φ * z) * W z)) := by
  let g : ℝ → ℝ := fun z => Real.exp (-φ * z) * W z
  have hgpos : ∀ z : ℝ, 0 < z → 0 < g z := by
    intro z hz
    exact mul_pos (Real.exp_pos _) 
      ((scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv) z hz)
  have hgdiff : ∀ z : ℝ, 0 < z → HasDerivAt g (deriv g z) z := by
    intro z hz
    have hlin : DifferentiableAt ℝ (fun t : ℝ => -(φ * t)) z := by
      fun_prop
    have hgf : g = (Real.exp ∘ (fun t : ℝ => -(φ * t))) * W := by
      funext t
      change Real.exp (-φ * t) * W t = Real.exp (-(φ * t)) * W t
      rw [neg_mul]
    rw [hgf]
    exact ((Real.differentiableAt_exp.comp z hlin).mul (hWdiff z hz)).hasDerivAt
  apply positive_cross_derivative_log_concavity g hgpos hgdiff
  intro x y hx hxy
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  exact unbounded_tilted_scale_cross_derivative_of_corrected_exit
    X q hq W hW hnbv hExit φ x y hx hxy (hWdiff x hx) (hWdiff y hy)
