-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_support_unbounded_clock_tail_increment_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T07:56:20.489799+00:00
-- url     : https://prove2.me/submissions/e533f45b-d9ce-4295-9362-f5c1f77fc828

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Exponential
import Theorems.Thm_AvramDividend_Classical_esscher_random_time_joint_past_clock_future_factorization
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_cylinder_factor
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Genuine random-time Esscher stopped-increment factorisation on an
unbounded upper tail of the independent exponential clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (u : ℝ≥0)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (B : Set ℝ) (hB : MeasurableSet B)
    (hEventAdapted : MeasurableSet[𝓕 (H + 1 + u)]
      (A ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}))
    (C : Set ℝ) (hC : MeasurableSet C)
    (hClockLow : ∀ t ∈ C, H + 1 + u ≤ Real.toNNReal t)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X z.2.toNNReal z.1 -
        (z.2.toNNReal : ℝ) * X.ψ θ)))) :
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X z.2.toNNReal z.1 -
          (z.2.toNNReal : ℝ) * X.ψ θ))))
      ((A ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) ×ˢ C) =
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X (H + 1 + u) ω -
        ((H + 1 + u : ℝ≥0) : ℝ) * X.ψ θ)))) A *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
          ((X.X u) ⁻¹' B)) * (expMeasure p) C := by
  have hPast :=
    esscher_random_time_joint_past_clock_future_factorization
      X θ p hθ hp (H + 1 + u) hJoint
      (A ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B})
      hEventAdapted C hC hClockLow
  rw [esscher_bounded_stop_future_increment_cylinder_factor
    X θ hθ τ hstop H hbound u (H + 1 + u)
    (le_refl _) A hA B hB] at hPast
  exact hPast
