-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_two_sided_terminal_payoff_pointwise_bound_of_Wzero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:07:55.816254+00:00
-- url     : https://prove2.me/submissions/8a86ffa2-ea6b-4d9d-91b5-604aa535fbd4

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_scale_creeping_atom
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_pointwise_bound
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Uniform bound for the sum of both strict two-sided terminal
scale payoffs. The lower payoff vanishes pointwise when W(0)=0;
the upper payoff is bounded by W(a) for non-negative discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hWzero : W 0 = 0)
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
  have hLower : (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0) = 0 := by
    rw [chat04_lower_exit_scale_creeping_atom X q W hW a x ω]
    simp [hWzero]
  rw [hLower, add_zero]
  exact chat04_strict_stopped_exit_payoff_pointwise_bound
    X q hq a x hxa W ω
