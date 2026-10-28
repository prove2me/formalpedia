-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_finiteStopping_full_futurePath_esscher_reward_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:55:57.428242+00:00
-- url     : https://prove2.me/submissions/b9293b1f-5f50-4fbf-a98d-19fd1c6a898a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_historyWeight_futureReward_factor

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

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
  have hr' : Measurable fun path : ℝ≥0 → ℝ =>
      ENNReal.ofReal (Real.exp (θ * path u - (u : ℝ) * X.ψ θ)) * reward path :=
    (ENNReal.measurable_ofReal.comp
      ((measurable_const.mul (measurable_pi_apply u)).sub measurable_const).exp).mul hr
  exact AvramDividend.Classical.levy_finiteStopping_historyWeight_futureReward_factor
    X τ hτ pastWeight hp hpPast
    (fun path => ENNReal.ofReal (Real.exp (θ * path u - (u : ℝ) * X.ψ θ)) * reward path) hr'
