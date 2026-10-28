-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_actual_Qp_stopped_clock_fullPath_esscher_shift_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T11:48:48.334956+00:00
-- url     : https://prove2.me/submissions/2d9a8c9e-7010-4058-bad6-d643b59b74bd

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_exp_clock_random_age_joint_reward_shift_ws01d

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Exact joint terminal Esscher clock shift preserving the stopped prefix and
entire post-age path, without imposing full-path Qp independence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hp : 0 < p)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (W : Ω → ℝ≥0∞)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hJoint : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp
        (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (hObserve : Measurable (fun z : Ω × ℝ =>
      W z.1 * H (Real.toNNReal (z.2 - (τ z.1 : ℝ)))
        (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)))
    (hReward : Measurable (fun z : Ω × ℝ =>
      (W z.1 * ENNReal.ofReal (Real.exp
        (θ * X.X (τ z.1) z.1 - (τ z.1 : ℝ) * X.ψ θ))) *
      (ENNReal.ofReal (Real.exp
        (θ * (X.X (τ z.1 + Real.toNNReal z.2) z.1 -
          X.X (τ z.1) z.1) -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ)) *
        H (Real.toNNReal z.2)
          (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 -
            X.X (τ z.1) z.1))))
    (hSplit : ∀ (ω : Ω) (t : ℝ), (τ ω : ℝ) ≤ t →
      ENNReal.ofReal (Real.exp
        (θ * X.X (Real.toNNReal t) ω -
          (Real.toNNReal t : ℝ) * X.ψ θ)) =
      ENNReal.ofReal (Real.exp
        (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)) *
      ENNReal.ofReal (Real.exp
        (θ * (X.X (τ ω + Real.toNNReal (t - (τ ω : ℝ))) ω -
          X.X (τ ω) ω) -
          (Real.toNNReal (t - (τ ω : ℝ)) : ℝ) * X.ψ θ))) :
    (∫⁻ z : Ω × ℝ,
      if (τ z.1 : ℝ) ≤ z.2 then
        W z.1 * H (Real.toNNReal (z.2 - (τ z.1 : ℝ)))
          (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 -
            X.X (τ z.1) z.1)
      else 0
      ∂((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ))))) =
    (∫⁻ ω : Ω,
      ENNReal.ofReal (Real.exp (-(p * (τ ω : ℝ)))) *
      (∫⁻ u : ℝ,
        (W ω * ENNReal.ofReal (Real.exp
          (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ))) *
        (ENNReal.ofReal (Real.exp
          (θ * (X.X (τ ω + Real.toNNReal u) ω - X.X (τ ω) ω) -
            (Real.toNNReal u : ℝ) * X.ψ θ)) *
          H (Real.toNNReal u)
            (fun s : ℝ≥0 => X.X (τ ω + s) ω - X.X (τ ω) ω))
        ∂(expMeasure p)) ∂P)  := by
  let dens : Ω × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp
      (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))
  let f : Ω × ℝ → ℝ≥0∞ := fun z =>
    if (τ z.1 : ℝ) ≤ z.2 then
      W z.1 * H (Real.toNNReal (z.2 - (τ z.1 : ℝ)))
        (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)
    else 0
  let reward : Ω × ℝ → ℝ≥0∞ := fun z =>
    (W z.1 * ENNReal.ofReal (Real.exp
      (θ * X.X (τ z.1) z.1 - (τ z.1 : ℝ) * X.ψ θ))) *
    (ENNReal.ofReal (Real.exp
      (θ * (X.X (τ z.1 + Real.toNNReal z.2) z.1 -
        X.X (τ z.1) z.1) -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ)) *
      H (Real.toNNReal z.2)
        (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 -
          X.X (τ z.1) z.1))
  have hAgeReal : Measurable (fun ω : Ω => (τ ω : ℝ)) :=
    hτ.coe_nnreal_real
  have hS : MeasurableSet {z : Ω × ℝ | (τ z.1 : ℝ) ≤ z.2} := by
    exact measurableSet_le
      (hAgeReal.comp measurable_fst) measurable_snd
  have hf : Measurable f := by
    change Measurable (fun z : Ω × ℝ =>
      if (τ z.1 : ℝ) ≤ z.2 then
        W z.1 * H (Real.toNNReal (z.2 - (τ z.1 : ℝ)))
          (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 -
            X.X (τ z.1) z.1)
      else 0)
    exact hObserve.ite hS measurable_const
  have hdens : Measurable dens := hJoint
  have hr : Measurable reward := hReward
  change (∫⁻ z : Ω × ℝ, f z ∂((P.prod (expMeasure p)).withDensity dens)) = _
  calc
    (∫⁻ z : Ω × ℝ, f z
      ∂((P.prod (expMeasure p)).withDensity dens)) =
      (∫⁻ z : Ω × ℝ, dens z * f z
        ∂(P.prod (expMeasure p))) := by
      exact lintegral_withDensity_eq_lintegral_mul
        (P.prod (expMeasure p)) hdens hf
    _ = (∫⁻ z : Ω × ℝ,
        if (τ z.1 : ℝ) ≤ z.2 then
          reward (z.1, z.2 - (τ z.1 : ℝ)) else 0
          ∂(P.prod (expMeasure p))) := by
      apply lintegral_congr
      intro z
      by_cases hz : (τ z.1 : ℝ) ≤ z.2
      · simp only [dens, f, reward, if_pos hz]
        rw [hSplit z.1 z.2 hz]
        ac_rfl
      · simp [f, hz]
    _ = _ := by
      exact exp_clock_random_age_joint_reward_shift_ws01d
        P p hp τ hτ reward hr
