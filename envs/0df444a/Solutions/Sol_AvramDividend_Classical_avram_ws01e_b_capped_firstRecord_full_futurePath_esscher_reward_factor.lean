-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_capped_firstRecord_full_futurePath_esscher_reward_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T11:20:39.904892+00:00
-- url     : https://prove2.me/submissions/2e7661d7-5025-4a9c-9bb5-d2b30789a702

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_firstRecord_uncensored_discountedFutureReward_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Esscher-weighted whole future-path strong Markov reward on genuine
uncensored capped first upper records. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (N u : ℝ≥0)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω :=
       {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)}
     (∫⁻ ω, if ω ∈ A then discount (τ ω) *
       (ENNReal.ofReal (Real.exp
         (θ * (X.X (τ ω + u) ω - X.X (τ ω) ω) -
           (u : ℝ) * X.ψ θ)) *
         reward (fun t : ℝ≥0 =>
           X.X (τ ω + t) ω - X.X (τ ω) ω))
       else 0 ∂P) =
       (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
         (∫⁻ ω, ENNReal.ofReal (Real.exp
           (θ * X.X u ω - (u : ℝ) * X.ψ θ)) *
           reward (fun t : ℝ≥0 => X.X t ω) ∂P)) := by
  let G : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun f =>
    ENNReal.ofReal (Real.exp (θ * f u - (u : ℝ) * X.ψ θ)) * reward f
  have hEval : Measurable (fun f : ℝ≥0 → ℝ => f u) :=
    measurable_pi_apply u
  have hG : Measurable G := by
    dsimp [G]
    exact (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        ((measurable_const.mul hEval).sub measurable_const))).mul hr
  have hFactor :=
    avram_ws01e_b_support_firstRecord_uncensored_discountedFutureReward_factor
      X b N discount hd G hG
  simpa only [G] using hFactor
