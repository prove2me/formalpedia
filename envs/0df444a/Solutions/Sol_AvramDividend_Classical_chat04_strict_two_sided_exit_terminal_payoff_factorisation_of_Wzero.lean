-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_two_sided_exit_terminal_payoff_factorisation_of_Wzero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:02:32.689269+00:00
-- url     : https://prove2.me/submissions/798e08ae-e3bd-4cb7-bc47-ddbafe4b1a44

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_payoff
import Theorems.Thm_AvramDividend_Classical_chat03_exact_upperfirst_discount_integrand_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_lintegral_factorisation
import Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_lintegral_zero_of_Wzero
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Combining upper-exit and lower-ruin stopped terminal scale payoffs.
The lower contribution vanishes when the scale function is zero at zero.
The remaining contribution is the strict upper-exit discount times W(a).
This is the boundary-payoff component of the killed martingale argument. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hWzero : W 0 = 0)
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
      else 0) ∂P) =
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) := by
  have hmDiscount : Measurable (fun ω : Ω => (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0)) :=
    chat03_exact_upperfirst_discount_integrand_measurable X (-x) (a - x) q
  have hmUpper : Measurable (fun ω : Ω => (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0)) := by
    have heq :
      (fun ω : Ω => (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0)) =
      (fun ω : Ω => (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0) * ENNReal.ofReal (W a)) := by
        funext ω
        simpa only [ite_mul, zero_mul] using
          (chat04_strict_upper_exit_scale_payoff X W q a x hxa ω)
    rw [heq]
    exact hmDiscount.mul_const _
  rw [lintegral_add_left hmUpper]
  rw [chat04_lower_exit_lintegral_zero_of_Wzero X q W hW hWzero a x, add_zero]
  exact chat04_strict_stopped_exit_payoff_lintegral_factorisation X q a x hxa W
