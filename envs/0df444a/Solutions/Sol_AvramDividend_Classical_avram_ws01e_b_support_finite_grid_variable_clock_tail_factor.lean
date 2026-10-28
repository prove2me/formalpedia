-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_support_finite_grid_variable_clock_tail_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:05:28.136802+00:00
-- url     : https://prove2.me/submissions/051e7816-2d39-4770-bd0d-4b1f111694e3

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

/-- Actual random-terminal Esscher factorisation over grid-dependent
clock tails, with no common future terminal horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0) (u : ℝ≥0)
    (A : Set Ω)
    (hHistory : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 s) (A ∩ {ω : Ω | τ ω = s}))
    (B : Set ℝ) (hB : MeasurableSet B)
    (hAdapted : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 (s + u))
        ((A ∩ {ω : Ω | τ ω = s}) ∩
          (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B))
    (C : ℝ≥0 → Set ℝ)
    (hC : ∀ s ∈ grid, MeasurableSet (C s))
    (hClockTail : ∀ s ∈ grid, ∀ t ∈ C s,
      s + u ≤ Real.toNNReal t)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) :
    (∑ s ∈ grid,
      ((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
        (((A ∩ {ω : Ω | τ ω = s}) ∩
          (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B) ×ˢ C s)) =
    ∑ s ∈ grid,
      ((P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))))
          (A ∩ {ω : Ω | τ ω = s}) *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
          ((X.X u) ⁻¹' B)) * (expMeasure p) (C s) := by
  classical
  apply Finset.sum_congr rfl
  intro s hs
  have hPast :=
    esscher_random_time_joint_past_clock_future_factorization
      X θ p hθ hp (s + u) hJoint
      ((A ∩ {ω : Ω | τ ω = s}) ∩
        (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B)
      (hAdapted s hs) (C s) (hC s hs) (hClockTail s hs)
  rw [esscher_terminal_increment_cylinder_factorization
    X θ hθ s u (s + u) (le_refl _)
    (A ∩ {ω : Ω | τ ω = s}) (hHistory s hs) B hB] at hPast
  exact hPast
