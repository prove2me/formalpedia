-- Prove2me | solution 1 for AvramDividend.Classical.chat04_stopped_scale_exit_payoff_antitone_discount_any_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T12:02:37.91756+00:00
-- url     : https://prove2.me/submissions/b676da7a-b194-4504-9cfa-f66d9a8fd24e

import Mathlib.Tactic.GCongr
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_any_measure_factorisation
import Theorems.Thm_AvramDividend_Classical_chat04_joint_discounted_exit_any_measure_comparison

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- The arbitrary-law stopped scale exit value is antitone in the discount rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (q₁ q₂ a x : ℝ) (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂)
    (hxa : x ≤ a) (W : ℝ → ℝ) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q₂ * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂μ) ≤ (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q₁ * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂μ) := by
  rw [chat04_strict_stopped_exit_payoff_any_measure_factorisation
        X μ q₂ a x hxa W,
      chat04_strict_stopped_exit_payoff_any_measure_factorisation
        X μ q₁ a x hxa W]
  have hdisc :=
    chat04_joint_discounted_exit_any_measure_comparison
      X μ q₁ q₂ a a x x hq₁ hq (le_refl x) (le_refl (a - x))
  gcongr
  all_goals exact hdisc
