-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_esscher_survival_finite_markov_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:18:24.619044+00:00
-- url     : https://prove2.me/submissions/c93a4be2-878a-4e5f-be1a-763da683b574

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_finite_survival_markov_product
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_esscher_fresh_path_survival_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_history_survival_pair_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_future_reserve_survival_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Exact original-P finite-time survival Markov kernel, with the fresh
Esscher survival payoff converted from the full path law to a real integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) (s u : ℝ≥0)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = u) :
    (∫⁻ ω, ({ω | ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + X.X v ω}).indicator
      (fun ω => ENNReal.ofReal (Real.exp
        (θ * X.X (s + u) ω - ((s + u : ℝ≥0) : ℝ) *
          laplaceExponent X.c X.σ X.ν θ))) ω ∂P) =
    (∫⁻ h : ℝ × Bool,
      (if h.2 then
        ENNReal.ofReal (Real.exp
          (θ * h.1 - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ)) *
        ENNReal.ofReal (∫ ω,
          ({ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ (x + h.1) + X.X v ω}).indicator
            (fun ω => Real.exp
              (θ * X.X u ω - (u : ℝ) *
                laplaceExponent X.c X.σ X.ν θ)) ω ∂P)
       else (0 : ℝ≥0∞))
      ∂(Measure.map (fun ω : Ω => (X.X s ω,
        decide (∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω))) P)) := by
  classical
  have hH := avram_ws01e_integrator_new_history_survival_pair_measurable
    X x s τ hCover
  have hProduct := avram_ws01e_integrator_new_finite_survival_markov_product
    X θ x s u τ hCover hTerminal hH
  rw [hProduct]
  apply lintegral_congr
  intro h
  rcases h with ⟨z, b⟩
  cases b with
  | false => simp
  | true =>
      simp only [ite_true]
      let A : ℝ := Real.exp
        (θ * z - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ)
      have hA : 0 ≤ A := (Real.exp_pos _).le
      let V : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun y =>
        if ∀ j : ℕ, τ j ≤ u → 0 ≤ (x + z) + y (τ j) then
          ENNReal.ofReal (Real.exp
            (θ * y u - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ))
        else 0
      have hPair : Measurable (fun y : ℝ≥0 → ℝ => (x + z, y)) :=
        measurable_const.prodMk measurable_id
      have hEvent : MeasurableSet
          {y : ℝ≥0 → ℝ | ∀ j : ℕ, τ j ≤ u → 0 ≤ (x + z) + y (τ j)} := by
        simpa only [preimage, mem_setOf_eq] using
          (chat04_countable_shifted_future_reserve_survival_measurable
            τ u).preimage hPair
      have hReward : Measurable (fun y : ℝ≥0 → ℝ =>
          ENNReal.ofReal (Real.exp
            (θ * y u - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ))) :=
        ENNReal.measurable_ofReal.comp
          (Real.continuous_exp.measurable.comp
            ((measurable_const.mul (measurable_pi_apply u)).sub measurable_const))
      have hV : Measurable V := Measurable.ite hEvent hReward measurable_const
      have hPoint (y : ℝ≥0 → ℝ) :
          (if ∀ j : ℕ, τ j ≤ u → 0 ≤ (x + z) + y (τ j) then
            ENNReal.ofReal (A * Real.exp
              (θ * y u - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ))
          else 0) = ENNReal.ofReal A * V y := by
        by_cases hc : ∀ j : ℕ, τ j ≤ u → 0 ≤ (x + z) + y (τ j)
        · simp [V, hc, ENNReal.ofReal_mul hA]
        · simp [V, hc]
      calc
        (∫⁻ y : ℝ≥0 → ℝ, (if ∀ j : ℕ,
            τ j ≤ u → 0 ≤ (x + z) + y (τ j) then
            ENNReal.ofReal (A * Real.exp
              (θ * y u - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ))
          else 0) ∂(Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) =
          (∫⁻ y : ℝ≥0 → ℝ, ENNReal.ofReal A * V y
             ∂(Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
          apply lintegral_congr
          intro y
          exact hPoint y
        _ = ENNReal.ofReal A * (∫⁻ y : ℝ≥0 → ℝ, V y
             ∂(Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
          rw [lintegral_const_mul]
          exact hV
        _ = _ := by
          rw [show (∫⁻ y : ℝ≥0 → ℝ, V y
             ∂(Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) =
            ENNReal.ofReal (∫ ω,
              ({ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ (x + z) + X.X v ω}).indicator
                (fun ω => Real.exp (θ * X.X u ω -
                   (u : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) from
            avram_ws01e_integrator_new_esscher_fresh_path_survival_lintegral
              X θ hθ (x + z) u τ hCover hTerminal]
