-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_tilted_scale_cross_derivative_of_corrected_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:44:58.776312+00:00
-- url     : https://prove2.me/submissions/8d682dc7-2842-46ba-a695-7f015cb81b29

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_cross_derivative_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_exponential_tilt_preserves_cross_derivative_order
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The corrected killed-exit identity gives local tilted-scale log-slope order. -/
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
    (φ x y : ℝ) (hx : 0 < x) (hxy : x ≤ y)
    (hdx : DifferentiableAt ℝ W x)
    (hdy : DifferentiableAt ℝ W y) :
    deriv (fun z : ℝ => Real.exp (-φ * z) * W z) y *
        (Real.exp (-φ * x) * W x) ≤
      deriv (fun z : ℝ => Real.exp (-φ * z) * W z) x *
        (Real.exp (-φ * y) * W y) := by
  have hcross := unbounded_scale_cross_derivative_of_corrected_exit
    X q hq W hW hnbv hExit x y hx hxy hdx hdy
  exact exponential_tilt_preserves_cross_derivative_order
    W φ x y hcross hdx hdy
