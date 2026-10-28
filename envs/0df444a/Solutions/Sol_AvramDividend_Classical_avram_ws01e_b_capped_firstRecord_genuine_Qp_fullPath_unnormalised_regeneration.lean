-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_capped_firstRecord_genuine_Qp_fullPath_unnormalised_regeneration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:43:24.498076+00:00
-- url     : https://prove2.me/submissions/0c227b52-b929-43e5-8ee9-be1c96989e05

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_stopped_clock_fullPath_esscher_shift_integral
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_capped_firstRecord_exp_clock_fullPath_esscher_mixture

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- True capped upper-record Qp unnormalised residual-clock/future-path
regeneration, by actual terminally tilted clock shift and Tonelli. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (N : ℝ≥0)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (τ : Ω → ℝ≥0) (A : Set Ω)
    [hDec : DecidablePred (fun ω : Ω => ω ∈ A)]
    (hτdef : τ = fun ω =>
      (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal)
    (hAdef : A =
      {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)})
    (hτ : Measurable τ) (hA : MeasurableSet A)
    (W : Ω → ℝ≥0∞)
    (hW : ∀ ω : Ω, W ω = if ω ∈ A then 1 else 0)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (hWeight : ∀ ω : Ω, ω ∈ A →
      ENNReal.ofReal (Real.exp (-(p * (τ ω : ℝ)))) * ENNReal.ofReal (Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)) = discount (τ ω))
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : ∀ u : ℝ≥0, Measurable (H u))
    (hRMeas : Measurable (fun r : ℝ =>
      (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal r) ω - (Real.toNNReal r : ℝ) * X.ψ θ)) * H (Real.toNNReal r) (fun t : ℝ≥0 => X.X t ω) ∂P)))
    (hPostMeas : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp (θ * (X.X (τ z.1 + Real.toNNReal z.2) z.1 - X.X (τ z.1) z.1) - (Real.toNNReal z.2 : ℝ) * X.ψ θ)) *
      H (Real.toNNReal z.2) (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)))
    (hJoint : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 - (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (hObserve : Measurable (fun z : Ω × ℝ =>
      W z.1 * H (Real.toNNReal (z.2 - (τ z.1 : ℝ))) (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)))
    (hReward : Measurable (fun z : Ω × ℝ =>
      (W z.1 * ENNReal.ofReal (Real.exp (θ * X.X (τ z.1) z.1 - (τ z.1 : ℝ) * X.ψ θ))) *
      (ENNReal.ofReal (Real.exp (θ * (X.X (τ z.1 + Real.toNNReal z.2) z.1 - X.X (τ z.1) z.1) - (Real.toNNReal z.2 : ℝ) * X.ψ θ)) * H (Real.toNNReal z.2) (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1))))
    (hSplit : ∀ (ω : Ω) (t : ℝ), (τ ω : ℝ) ≤ t →
      ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal t) ω - (Real.toNNReal t : ℝ) * X.ψ θ)) =
      ENNReal.ofReal (Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)) *
      ENNReal.ofReal (Real.exp (θ * (X.X (τ ω + Real.toNNReal (t - (τ ω : ℝ))) ω - X.X (τ ω) ω) - (Real.toNNReal (t - (τ ω : ℝ)) : ℝ) * X.ψ θ))) :
    (∫⁻ z : Ω × ℝ,
      if (τ z.1 : ℝ) ≤ z.2 then W z.1 * H (Real.toNNReal (z.2 - (τ z.1 : ℝ))) (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)
      else 0
      ∂((P.prod (expMeasure p)).withDensity (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 - (Real.toNNReal z.2 : ℝ) * X.ψ θ))))) =
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
      (∫⁻ r : ℝ, (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal r) ω - (Real.toNNReal r : ℝ) * X.ψ θ)) * H (Real.toNNReal r) (fun t : ℝ≥0 => X.X t ω) ∂P) ∂(expMeasure p))  := by
  letI : IsProbabilityMeasure (expMeasure p) :=
    isProbabilityMeasure_expMeasure hp
  let Zpre : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (Real.exp
      (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ))
  let post : Ω → ℝ → ℝ≥0∞ := fun ω u =>
    ENNReal.ofReal (Real.exp
      (θ * (X.X (τ ω + Real.toNNReal u) ω - X.X (τ ω) ω) -
        (Real.toNNReal u : ℝ) * X.ψ θ)) *
    H (Real.toNNReal u)
      (fun s : ℝ≥0 => X.X (τ ω + s) ω - X.X (τ ω) ω)
  have hPostω (ω : Ω) : Measurable (post ω) := by
    let k : ℝ → Ω × ℝ := fun u => (ω, u)
    have hk : Measurable k := measurable_const.prodMk measurable_id
    simpa only [Function.comp_def] using hPostMeas.comp hk
  have hInner (ω : Ω) :
      (∫⁻ u : ℝ, (W ω * Zpre ω) * post ω u ∂(expMeasure p)) =
        (W ω * Zpre ω) * (∫⁻ u : ℝ, post ω u ∂(expMeasure p)) :=
    lintegral_const_mul (W ω * Zpre ω) (hPostω ω)
  have hLine (ω : Ω) :
      ENNReal.ofReal (Real.exp (-(p * (τ ω : ℝ)))) *
        (∫⁻ u : ℝ, (W ω * Zpre ω) * post ω u ∂(expMeasure p)) =
      if ω ∈ A then discount (τ ω) *
        (∫⁻ u : ℝ, post ω u ∂(expMeasure p)) else 0 := by
    rw [hInner ω]
    by_cases ha : ω ∈ A
    · rw [hW ω]
      simp only [if_pos ha, one_mul]
      calc
        _ = (ENNReal.ofReal (Real.exp (-(p * (τ ω : ℝ)))) *
              Zpre ω) * (∫⁻ u : ℝ, post ω u ∂(expMeasure p)) := by
          ac_rfl
        _ = _ := by
          rw [show ENNReal.ofReal (Real.exp (-(p * (τ ω : ℝ)))) *
              Zpre ω = discount (τ ω) from hWeight ω ha]
    · rw [hW ω]
      simp [ha]
  have hG : Measurable (fun z : Ω × ℝ =>
      if z.1 ∈ A then discount (τ z.1) * post z.1 z.2 else 0) := by
    have hdτ : Measurable (fun z : Ω × ℝ => discount (τ z.1)) :=
      (hd.comp hτ).comp measurable_fst
    have hpst : Measurable (fun z : Ω × ℝ => post z.1 z.2) := by
      simpa only [post] using hPostMeas
    exact (hdτ.mul hpst).ite (hA.preimage measurable_fst) measurable_const
  have hSwapω (ω : Ω) :
      (∫⁻ u : ℝ, (if ω ∈ A then discount (τ ω) * post ω u else 0)
          ∂(expMeasure p)) =
      if ω ∈ A then discount (τ ω) *
        (∫⁻ u : ℝ, post ω u ∂(expMeasure p)) else 0 := by
    by_cases ha : ω ∈ A
    · simp only [if_pos ha]
      exact lintegral_const_mul (discount (τ ω)) (hPostω ω)
    · simp [ha]
  have hShift :=
    avram_ws01e_b_actual_Qp_stopped_clock_fullPath_esscher_shift_integral
      X θ p hp τ hτ W H hJoint hObserve hReward hSplit
  have hMixture :=
    avram_ws01e_b_capped_firstRecord_exp_clock_fullPath_esscher_mixture
      X b N θ p hθ hp discount hd H hH hRMeas
  calc
    _ = (∫⁻ ω : Ω,
      ENNReal.ofReal (Real.exp (-(p * (τ ω : ℝ)))) *
      (∫⁻ u : ℝ, (W ω * Zpre ω) * post ω u ∂(expMeasure p)) ∂P) := by
        simpa only [Zpre, post] using hShift
    _ = (∫⁻ ω : Ω,
      if ω ∈ A then discount (τ ω) *
        (∫⁻ u : ℝ, post ω u ∂(expMeasure p)) else 0 ∂P) := by
        apply lintegral_congr
        intro ω
        exact hLine ω
    _ = (∫⁻ u : ℝ, (∫⁻ ω : Ω,
      if ω ∈ A then discount (τ ω) * post ω u else 0 ∂P)
      ∂(expMeasure p)) := by
        calc
          _ = (∫⁻ ω : Ω, (∫⁻ u : ℝ,
            if ω ∈ A then discount (τ ω) * post ω u else 0
            ∂(expMeasure p)) ∂P) := by
              apply lintegral_congr
              intro ω
              exact (hSwapω ω).symm
          _ = _ := lintegral_lintegral_swap hG.aemeasurable
    _ = _ := by
      simpa only [hτdef, hAdef, post] using hMixture
