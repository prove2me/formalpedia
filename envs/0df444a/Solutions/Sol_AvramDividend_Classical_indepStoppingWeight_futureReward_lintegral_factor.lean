-- Prove2me | solution 1 for AvramDividend.Classical.indepStoppingWeight_futureReward_lintegral_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:56:57.682625+00:00
-- url     : https://prove2.me/submissions/3f502bc4-a24f-45cd-bce6-b48331f45773

import Mathlib.Probability.Independence.Integration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- An independent stopping clock separates any measurable time discount and future-path reward. -/
theorem solution
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (Y : Ω → β) (hY : Measurable Y)
    (hInd : IndepFun τ Y P)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : β → ℝ≥0∞) (hr : Measurable reward) :
    (∫⁻ ω, discount (τ ω) * reward (Y ω) ∂P) =
      (∫⁻ ω, discount (τ ω) ∂P) *
        (∫⁻ ω, reward (Y ω) ∂P) := by
  have hProduct : IndepFun (discount ∘ τ) (reward ∘ Y) P :=
    hInd.comp hd hr
  have hFactor :=
    lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
      (hd.comp hτ) (hr.comp hY) hProduct
  simpa only [Pi.mul_apply, Function.comp_apply] using hFactor
