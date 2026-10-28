-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_upper_exit_scale_terminal_payoff_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:07:49.433804+00:00
-- url     : https://prove2.me/submissions/f1ed7252-7f38-426f-be5d-a57d2c408db7

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_payoff
import Theorems.Thm_AvramDividend_Classical_chat03_exact_upperfirst_discount_integrand_measurable
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual strict upper-exit terminal q-scale payoff is measurable,
since spectral negativity makes its scale component equal to W(a). -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a x : ℝ) (hxa : x ≤ a)
    (W : ℝ → ℝ) :
    Measurable (fun ω : Ω => (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0)) := by
  have hm : Measurable (fun ω : Ω => (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0)) :=
    chat03_exact_upperfirst_discount_integrand_measurable X (-x) (a - x) q
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
  exact hm.mul_const _
