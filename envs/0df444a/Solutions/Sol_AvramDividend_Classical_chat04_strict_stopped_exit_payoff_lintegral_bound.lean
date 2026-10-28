-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_stopped_exit_payoff_lintegral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:31:08.198193+00:00
-- url     : https://prove2.me/submissions/7007865d-a671-44d6-8371-4ab88eb5396b

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_payoff
import Theorems.Thm_AvramDividend_Classical_chat03_exact_upperfirst_discount_integrand_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_exact_stopped_discount_mul_scale_le_scale
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- The strict upper-exit stopped q-scale payoff has finite expectation
dominated by the upper-barrier scale value under non-negative discount.
This uses the verified boundary, measurability and discount interfaces. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (a x : ℝ) (hxa : x ≤ a)
    (W : ℝ → ℝ) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂P) ≤ ENNReal.ofReal (W a) := by
  have hm : Measurable (fun ω : Ω =>
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0) :=
    chat03_exact_upperfirst_discount_integrand_measurable X (-x) (a - x) q
  have hPayoff :
      (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂P) =
        twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) := by
    calc
      _ = (∫⁻ ω,
          (if twoSidedExitUpTime X (a - x) ω <
                twoSidedExitDownTime X (-x) ω then
            ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
          else 0) * ENNReal.ofReal (W a) ∂P) := by
        apply lintegral_congr
        intro ω
        simpa only [ite_mul, zero_mul] using
          (chat04_strict_upper_exit_scale_payoff X W q a x hxa ω)
      _ = twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) := by
        rw [lintegral_mul_const _ hm]
        rfl
  calc
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂P) =
        twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) := hPayoff
    _ ≤ ENNReal.ofReal (W a) :=
      chat03_exact_stopped_discount_mul_scale_le_scale
        X q hq (-x) (a - x) (W a)
