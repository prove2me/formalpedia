-- Prove2me | solution 1 for AvramDividend.Classical.chat04_zero_discount_stopped_scale_exit_payoff_any_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:46:07.90807+00:00
-- url     : https://prove2.me/submissions/03bbcabb-8a8e-4581-90db-8fca89b77c41

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_any_measure_factorisation
import Theorems.Thm_AvramDividend_Classical_chat04_zero_discount_upperfirst_mass_any_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- At zero discount, killed stopped scale value is barrier scale times the upper-first event mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (a x : ℝ) (hxa : x ≤ a) (W : ℝ → ℝ) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(0 * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂μ) =
      μ {ω : Ω | twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω} * ENNReal.ofReal (W a) := by
  calc
    _ = (∫⁻ ω,
        if twoSidedExitUpTime X (a - x) ω <
            twoSidedExitDownTime X (-x) ω then
          ENNReal.ofReal
            (Real.exp (-(0 * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
        else 0 ∂μ) * ENNReal.ofReal (W a) :=
          chat04_strict_stopped_exit_payoff_any_measure_factorisation
            X μ 0 a x hxa W
    _ = μ {ω : Ω | twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω} * ENNReal.ofReal (W a) := by
          rw [chat04_zero_discount_upperfirst_mass_any_measure X μ a x]
