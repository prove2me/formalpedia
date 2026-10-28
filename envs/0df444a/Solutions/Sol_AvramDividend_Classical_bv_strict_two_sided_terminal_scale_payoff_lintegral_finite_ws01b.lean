-- Prove2me | solution 1 for AvramDividend.Classical.bv_strict_two_sided_terminal_scale_payoff_lintegral_finite_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:25:09.455907+00:00
-- url     : https://prove2.me/submissions/ccaee889-e0db-4dfb-984f-4722da49085b

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_bv_two_sided_terminal_payoff_uniform_bound_ws01b
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The full strict two-sided BV terminal q-scale reward has finite expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
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
  letI : IsProbabilityMeasure P := X.isProbability
  calc
    _ ≤ (∫⁻ (_ : Ω), ENNReal.ofReal (W a) ∂P) := by
      apply lintegral_mono
      intro ω
      exact bv_two_sided_terminal_payoff_uniform_bound_ws01b
        X hBV q hq W hW a x ha hx hxa ω
    _ = ENNReal.ofReal (W a) := by simp
    _ < ⊤ := ENNReal.ofReal_lt_top
