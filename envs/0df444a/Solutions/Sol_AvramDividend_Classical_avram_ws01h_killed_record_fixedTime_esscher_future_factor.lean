-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_killed_record_fixedTime_esscher_future_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T13:02:39.161986+00:00
-- url     : https://prove2.me/submissions/963dace3-9da0-4717-aa34-6f88eb79fe33

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_original_killedRecord_fixedFuture_markov_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower b : ℝ) (N u : ℝ≥0)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω :=
       {ω | twoSidedExitUpTime X b ω < twoSidedExitDownTime X lower ω} ∩
       {ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}
     (∫⁻ ω, if ω ∈ A then discount (τ ω) *
       (ENNReal.ofReal (Real.exp
         (θ * (X.X (τ ω + u) ω - X.X (τ ω) ω) -
           (u : ℝ) * X.ψ θ)) *
         reward (fun t : ℝ≥0 => X.X (τ ω + t) ω - X.X (τ ω) ω))
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
    avram_ws01h_original_killedRecord_fixedFuture_markov_factor
      X lower b N discount hd G hG
  simpa only [G] using hFactor
