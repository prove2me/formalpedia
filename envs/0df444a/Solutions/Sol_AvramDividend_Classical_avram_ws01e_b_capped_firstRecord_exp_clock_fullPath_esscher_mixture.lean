-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_capped_firstRecord_exp_clock_fullPath_esscher_mixture
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T11:34:35.585988+00:00
-- url     : https://prove2.me/submissions/0670a3e3-31f6-46a7-ac4f-b493f4afaf04

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_capped_firstRecord_full_futurePath_esscher_reward_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Integrate the first-record full-fresh-path Esscher factor over actual
real Exp(p) clock ages, keeping arbitrary time-varying path reward sections. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (N : ℝ≥0)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : ∀ u : ℝ≥0, Measurable (H u))
    (hRMeas : Measurable (fun r : ℝ =>
      (∫⁻ ω, ENNReal.ofReal (Real.exp
        (θ * X.X (Real.toNNReal r) ω -
          (Real.toNNReal r : ℝ) * X.ψ θ)) *
        H (Real.toNNReal r) (fun t : ℝ≥0 => X.X t ω) ∂P))) :
    (∫⁻ r : ℝ,
      (let τ : Ω → ℝ≥0 := fun ω =>
         (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
       let A : Set Ω :=
         {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)}
       (∫⁻ ω, if ω ∈ A then discount (τ ω) *
         (ENNReal.ofReal (Real.exp
           (θ * (X.X (τ ω + Real.toNNReal r) ω - X.X (τ ω) ω) -
             (Real.toNNReal r : ℝ) * X.ψ θ)) *
          H (Real.toNNReal r) (fun t : ℝ≥0 =>
            X.X (τ ω + t) ω - X.X (τ ω) ω))
         else 0 ∂P)) ∂(expMeasure p)) =
      (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω :=
       {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)}
     (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P)) * (∫⁻ r : ℝ, (∫⁻ ω,
       ENNReal.ofReal (Real.exp
         (θ * X.X (Real.toNNReal r) ω -
           (Real.toNNReal r : ℝ) * X.ψ θ)) *
        H (Real.toNNReal r) (fun t : ℝ≥0 => X.X t ω) ∂P) ∂(expMeasure p))  := by
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
  let A : Set Ω := {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)}
  let mass : ℝ≥0∞ :=
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P)
  let L : ℝ → ℝ≥0∞ := fun r =>
    (∫⁻ ω, if ω ∈ A then discount (τ ω) *
      (ENNReal.ofReal (Real.exp
        (θ * (X.X (τ ω + Real.toNNReal r) ω - X.X (τ ω) ω) -
          (Real.toNNReal r : ℝ) * X.ψ θ)) *
        H (Real.toNNReal r) (fun t : ℝ≥0 =>
          X.X (τ ω + t) ω - X.X (τ ω) ω)) else 0 ∂P)
  let R : ℝ → ℝ≥0∞ := fun r =>
    (∫⁻ ω, ENNReal.ofReal (Real.exp
      (θ * X.X (Real.toNNReal r) ω -
        (Real.toNNReal r : ℝ) * X.ψ θ)) *
      H (Real.toNNReal r) (fun t : ℝ≥0 => X.X t ω) ∂P)
  change (∫⁻ r : ℝ, L r ∂(expMeasure p)) =
    mass * (∫⁻ r : ℝ, R r ∂(expMeasure p))
  have hEach (r : ℝ) : L r = mass * R r := by
    simpa only [L, R, mass, τ, A] using
      (avram_ws01e_b_capped_firstRecord_full_futurePath_esscher_reward_factor
        X b N (Real.toNNReal r) θ hθ discount hd
        (H (Real.toNNReal r)) (hH (Real.toNNReal r)))
  have hR : Measurable R := by
    simpa only [R] using hRMeas
  calc
    (∫⁻ r : ℝ, L r ∂(expMeasure p)) =
        (∫⁻ r : ℝ, mass * R r ∂(expMeasure p)) := by
      apply lintegral_congr
      intro r
      exact hEach r
    _ = mass * (∫⁻ r : ℝ, R r ∂(expMeasure p)) := by
      rw [lintegral_const_mul mass hR]
