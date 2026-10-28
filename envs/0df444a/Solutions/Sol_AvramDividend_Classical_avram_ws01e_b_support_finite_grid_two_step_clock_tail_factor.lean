-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_support_finite_grid_two_step_clock_tail_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:29:08.039338+00:00
-- url     : https://prove2.me/submissions/f1a8782f-2963-4450-aab4-e5f52eefc34d

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_random_time_joint_past_clock_future_factorization
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_cylinder_factorization

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
/-- Grid-dependent random-clock tails factor two successive
future increments from the adapted stopping-cell history. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0) (u v : ℝ≥0)
    (A : Set Ω)
    (hHistory : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 s) (A ∩ {ω : Ω | τ ω = s}))
    (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁)
    (hB₂ : MeasurableSet B₂)
    (hMiddle : ∀ s ∈ grid, @MeasurableSet Ω (𝓕 (s + u))
      ((A ∩ {ω : Ω | τ ω = s}) ∩
        (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B₁))
    (hFinal : ∀ s ∈ grid, @MeasurableSet Ω (𝓕 ((s + u) + v))
      (((A ∩ {ω : Ω | τ ω = s}) ∩
        (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B₁) ∩
        (fun ω : Ω => X.X ((s + u) + v) ω -
          X.X (s + u) ω) ⁻¹' B₂))
    (C : ℝ≥0 → Set ℝ)
    (hC : ∀ s ∈ grid, MeasurableSet (C s))
    (hClockTail : ∀ s ∈ grid, ∀ t ∈ C s,
      (s + u) + v ≤ Real.toNNReal t)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) :
    (∑ s ∈ grid,
      ((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
      ((((A ∩ {ω : Ω | τ ω = s}) ∩
        (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B₁) ∩
        (fun ω : Ω => X.X ((s + u) + v) ω -
          X.X (s + u) ω) ⁻¹' B₂) ×ˢ C s)) =
    ∑ s ∈ grid,
      ((((P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))))
          (A ∩ {ω : Ω | τ ω = s}) *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
          ((X.X u) ⁻¹' B₁)) *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X v ω - (v : ℝ) * X.ψ θ))))
          ((X.X v) ⁻¹' B₂)) * (expMeasure p) (C s)) := by
  classical
  apply Finset.sum_congr rfl
  intro s hs
  have hPast :=
    esscher_random_time_joint_past_clock_future_factorization
      X θ p hθ hp ((s + u) + v) hJoint
      (((A ∩ {ω : Ω | τ ω = s}) ∩
        (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B₁) ∩
        (fun ω : Ω => X.X ((s + u) + v) ω -
          X.X (s + u) ω) ⁻¹' B₂)
      (hFinal s hs) (C s) (hC s hs) (hClockTail s hs)
  rw [esscher_terminal_increment_cylinder_factorization
    X θ hθ (s + u) v ((s + u) + v) (le_refl _)
    ((A ∩ {ω : Ω | τ ω = s}) ∩
      (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B₁)
    (hMiddle s hs) B₂ hB₂] at hPast
  rw [esscher_terminal_increment_cylinder_factorization
    X θ hθ s u (s + u) (le_refl _)
    (A ∩ {ω : Ω | τ ω = s}) (hHistory s hs) B₁ hB₁] at hPast
  exact hPast
