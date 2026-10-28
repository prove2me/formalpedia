-- Prove2me | solution 1 for AvramDividend.Classical.strict_two_sided_terminal_scale_payoff_lintegral_finite_allvariation_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:31:12.275771+00:00
-- url     : https://prove2.me/submissions/7030fc4e-97bd-4870-872d-6aa6c1b021aa

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_bv_strict_two_sided_terminal_scale_payoff_lintegral_finite_ws01b
import Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_terminal_scale_payoff_lintegral_finite_unbounded
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The full stopped terminal q-scale reward is integrable in either variation regime. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      (if twoSidedExitUpTime X (a - x) ω <
           twoSidedExitDownTime X (-x) ω then
         ENNReal.ofReal
           (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
           ENNReal.ofReal
             (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
       else 0) +
      (if twoSidedExitDownTime X (-x) ω <
           twoSidedExitUpTime X (a - x) ω then
         ENNReal.ofReal
           (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
           ENNReal.ofReal
             (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
       else 0) ∂P) < ⊤ := by
  by_cases hBV : X.BoundedVariation
  · exact bv_strict_two_sided_terminal_scale_payoff_lintegral_finite_ws01b
      X hBV q hq W hW a x ha hx hxa
  · exact chat04_strict_two_sided_terminal_scale_payoff_lintegral_finite_unbounded
      X hBV q hq W hW a x hxa
