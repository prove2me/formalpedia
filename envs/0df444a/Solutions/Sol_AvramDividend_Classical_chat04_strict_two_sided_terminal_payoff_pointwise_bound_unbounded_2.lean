-- Prove2me | solution 2 for AvramDividend.Classical.chat04_strict_two_sided_terminal_payoff_pointwise_bound_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:21:09.64767+00:00
-- url     : https://prove2.me/submissions/e5823ae5-05a8-4524-864a-fc4357c79c25

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_terminal_payoff_pointwise_bound_of_Wzero
import Theorems.Thm_AvramDividend_Classical_unbounded_variation_gaussian_or_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_infinite_small_jumps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal

/-- Uniform pathwise bound for the entire two-sided stopped q-scale
terminal payoff in the unbounded-variation case. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (hxa : x ≤ a) (ω : Ω) :
    (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0) + (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0) ≤ ENNReal.ofReal (W a) := by
  have hWzero : W 0 = 0 := by
    by_cases hσ : 0 < X.σ
    · exact scaleFunction_zero_origin_gaussian_without_standing
        X q hq W hW hσ
    · have hinf :
          (∫⁻ y in Ioo (-1 : ℝ) 0,
            ENNReal.ofReal |y| ∂X.ν) = ⊤ :=
        (unbounded_variation_gaussian_or_infinite_small_jump_moment
          X hnbv).resolve_left hσ
      have hσ0 : X.σ = 0 :=
        le_antisymm (le_of_not_gt hσ) X.σ_nonneg
      exact scaleFunction_zero_origin_infinite_small_jumps
        X hσ0 hinf q hq W hW
  exact chat04_strict_two_sided_terminal_payoff_pointwise_bound_of_Wzero
    X q (le_of_lt hq) W hW hWzero a x hxa ω
