-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_two_sided_terminal_scale_payoff_lintegral_finite_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:21:21.982991+00:00
-- url     : https://prove2.me/submissions/36d616a8-587f-483c-9a9d-1fcc74ae7365

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_exit_terminal_payoff_factorisation_of_Wzero
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat03_exact_stopped_discount_mul_scale_le_scale
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- The complete strict two-sided terminal stopped q-scale payoff
has finite ENNReal expectation in the unbounded-variation case. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (hxa : x ≤ a) :
    (∫⁻ ω, (if twoSidedExitUpTime X (a - x) ω <
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
      else 0) ∂P) < ⊤ := by
  rw [chat04_strict_two_sided_exit_terminal_payoff_factorisation_of_Wzero
    X q W hW
    (chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW)
    a x hxa]
  exact lt_of_le_of_lt
    (chat03_exact_stopped_discount_mul_scale_le_scale
      X q (le_of_lt hq) (-x) (a - x) (W a))
    ENNReal.ofReal_lt_top
