-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_support_two_step_random_clock_future_increment_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:25:05.553009+00:00
-- url     : https://prove2.me/submissions/7a5abc97-ea40-4011-bd7e-3799fd91c93a

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Exponential
import Theorems.Thm_AvramDividend_Classical_esscher_random_time_joint_past_clock_future_factorization
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_cylinder_factorization

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Two consecutive future-increment cylinders factor under the actual
random-clock Esscher law on a clock tail beyond both increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (s u v : ℝ≥0)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A)
    (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁)
    (hB₂ : MeasurableSet B₂)
    (hMiddle : @MeasurableSet Ω (𝓕 (s + u))
      (A ∩ (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B₁))
    (hFinal : @MeasurableSet Ω (𝓕 ((s + u) + v))
      ((A ∩ (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B₁) ∩
        (fun ω : Ω => X.X ((s + u) + v) ω -
          X.X (s + u) ω) ⁻¹' B₂))
    (C : Set ℝ) (hC : MeasurableSet C)
    (hClockTail : ∀ t ∈ C, (s + u) + v ≤ Real.toNNReal t)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) :
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
      (((A ∩ (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B₁) ∩
        (fun ω : Ω => X.X ((s + u) + v) ω -
          X.X (s + u) ω) ⁻¹' B₂) ×ˢ C) =
    (((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)))) A *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
          ((X.X u) ⁻¹' B₁)) *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X v ω - (v : ℝ) * X.ψ θ))))
          ((X.X v) ⁻¹' B₂)) * (expMeasure p) C := by
  have hPast :=
    esscher_random_time_joint_past_clock_future_factorization
      X θ p hθ hp ((s + u) + v) hJoint
      ((A ∩ (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B₁) ∩
        (fun ω : Ω => X.X ((s + u) + v) ω -
          X.X (s + u) ω) ⁻¹' B₂)
      hFinal C hC hClockTail
  rw [esscher_terminal_increment_cylinder_factorization
    X θ hθ (s + u) v ((s + u) + v) (le_refl _)
    (A ∩ (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B₁)
    hMiddle B₂ hB₂] at hPast
  rw [esscher_terminal_increment_cylinder_factorization
    X θ hθ s u (s + u) (le_refl _) A hA B₁ hB₁] at hPast
  exact hPast
