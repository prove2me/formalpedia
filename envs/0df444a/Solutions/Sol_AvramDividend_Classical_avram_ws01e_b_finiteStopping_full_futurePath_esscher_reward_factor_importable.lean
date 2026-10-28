-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_finiteStopping_full_futurePath_esscher_reward_factor_importable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:47:42.360574+00:00
-- url     : https://prove2.me/submissions/0d212961-6f05-48cf-bd62-861f256729b9

import Mathlib
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_historyWeight_futureReward_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Full shifted Levy future-path Esscher reward factor at an arbitrary finite
stopping time, retaining any measurable stopped-history weight. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (pastWeight : Ω → ℝ≥0∞)
    (hp : Measurable pastWeight)
    (hpPast : Measurable[
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] pastWeight)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℝ≥0)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hr : Measurable reward) :
    (∫⁻ ω, pastWeight ω *
      (ENNReal.ofReal (Real.exp
        (θ * (X.X (τ ω + u) ω - X.X (τ ω) ω) -
          (u : ℝ) * X.ψ θ)) *
        reward (fun t : ℝ≥0 =>
          X.X (τ ω + t) ω - X.X (τ ω) ω)) ∂P) =
    (∫⁻ ω, pastWeight ω ∂P) *
      (∫⁻ ω, ENNReal.ofReal (Real.exp
        (θ * X.X u ω - (u : ℝ) * X.ψ θ)) *
        reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
  let G : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun f =>
    ENNReal.ofReal (Real.exp (θ * f u - (u : ℝ) * X.ψ θ)) * reward f
  have hEval : Measurable (fun f : ℝ≥0 → ℝ => f u) :=
    measurable_pi_apply u
  have hG : Measurable G := by
    dsimp [G]
    exact (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        ((measurable_const.mul hEval).sub measurable_const))).mul hr
  have hBase :=
    levy_finiteStopping_historyWeight_futureReward_factor
      X τ hτ pastWeight hp hpPast G hG
  simpa only [G] using hBase
