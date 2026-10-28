-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_tilted_grid_stopped_increment_independent_of_survival_history
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:31:54.530224+00:00
-- url     : https://prove2.me/submissions/8f5bf0f7-6fdb-44ca-bea5-d0ebc2f376cb

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_finite_grid_full_clock_event_factor
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0) (u : ℝ≥0)
    (A : Set Ω)
    (hHistory : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 s) (A ∩ {ω : Ω | τ ω = s}))
    (hBaseAdapted : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 (s + u))
        (A ∩ {ω : Ω | τ ω = s}))
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
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) {z : Ω × ℝ |
      z.1 ∈ A ∧ τ z.1 ∈ grid ∧
      X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1 ∈ B ∧
      z.2 ∈ C (τ z.1)} =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))) ((X.X u) ⁻¹' B) *
      ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) {z : Ω × ℝ |
      z.1 ∈ A ∧ τ z.1 ∈ grid ∧
      z.2 ∈ C (τ z.1)} := by
  have hAdaptedUniv : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 (s + u))
        ((A ∩ {ω : Ω | τ ω = s}) ∩
          (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' Set.univ) := by
    intro s hs
    simpa only [Set.preimage_univ, Set.inter_univ] using hBaseAdapted s hs
  have hFactorB :=
    avram_ws01e_b_support_finite_grid_full_clock_event_factor
      X θ p hθ hp τ grid u A hHistory B hB hAdapted
      C hC hClockTail hJoint
  have hFactorAll :=
    avram_ws01e_b_support_finite_grid_full_clock_event_factor
      X θ p hθ hp τ grid u A hHistory Set.univ MeasurableSet.univ
      hAdaptedUniv C hC hClockTail hJoint
  have hFreshOne :
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))) Set.univ = 1 := by
    letI : IsProbabilityMeasure
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))) := by
      exact chat04_esscher_weighted_finite_horizon_probability X u θ hθ
    exact measure_univ
  simp only [Set.mem_univ, true_and, Set.preimage_univ,
    hFreshOne, mul_one] at hFactorAll
  rw [hFactorB, hFactorAll]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  ac_rfl
