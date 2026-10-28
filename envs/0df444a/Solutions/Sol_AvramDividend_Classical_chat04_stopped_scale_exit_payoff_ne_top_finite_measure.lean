-- Prove2me | solution 1 for AvramDividend.Classical.chat04_stopped_scale_exit_payoff_ne_top_finite_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:40:18.366679+00:00
-- url     : https://prove2.me/submissions/e07b3f03-4807-4b17-8849-61e6cc5237b6

import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Data.ENNReal.Operations
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_any_measure_factorisation
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_upperfirst_lintegral_ne_top_finite_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- The killed stopped scale payoff has finite mass under a finite path law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (q a x : ℝ) (hq : 0 ≤ q) (hxa : x ≤ a) (W : ℝ → ℝ) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂μ) ≠ ⊤ := by
  rw [chat04_strict_stopped_exit_payoff_any_measure_factorisation
    X μ q a x hxa W]
  exact ENNReal.mul_ne_top
    (chat04_discounted_upperfirst_lintegral_ne_top_finite_measure
      X μ q a x hq)
    ENNReal.ofReal_ne_top
