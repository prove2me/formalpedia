-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_true_Qp_killed_rational_closed_event_measure_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T20:03:03.525416+00:00
-- url     : https://prove2.me/submissions/9b5bfd7c-a071-4097-813b-e48742378841

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_Qp_stopped_rational_closed_reward_integral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Use the genuine Qp stopped record rational/closed reward equality
as equality of the true measurable event masses. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (a : ℝ) (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (A : Set Ω) (hA : MeasurableSet A)
    (hGrid : MeasurableSet {z : Ω × ℝ |
      (τ z.1 : ℝ) ≤ z.2 ∧ z.1 ∈ A ∧
      ∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ <
          Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
        0 ≤ a + (X.X (τ z.1 + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) z.1 -
          X.X (τ z.1) z.1)})
    (hFull : MeasurableSet {z : Ω × ℝ |
      (τ z.1 : ℝ) ≤ z.2 ∧ z.1 ∈ A ∧
      ∀ u : ℝ≥0, u ≤ Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
        0 ≤ a + (X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1)}) :
    ((P.prod (expMeasure p)).withDensity
       (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) {z : Ω × ℝ |
      (τ z.1 : ℝ) ≤ z.2 ∧ z.1 ∈ A ∧
      ∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ <
          Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
        0 ≤ a + (X.X (τ z.1 + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) z.1 -
          X.X (τ z.1) z.1)} =
    ((P.prod (expMeasure p)).withDensity
       (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) {z : Ω × ℝ |
      (τ z.1 : ℝ) ≤ z.2 ∧ z.1 ∈ A ∧
      ∀ u : ℝ≥0, u ≤ Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
        0 ≤ a + (X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1)} := by
  classical
  have hAccepted :=
    avram_ws01h_actual_Qp_stopped_rational_closed_reward_integral
      X θ p hθ hp a τ hτ A hA
  dsimp only at hAccepted
  let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity
    (fun z => ENNReal.ofReal (Real.exp
      (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
  let G : Set (Ω × ℝ) := {z | (τ z.1 : ℝ) ≤ z.2 ∧ z.1 ∈ A ∧
    ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
      0 ≤ a + (X.X (τ z.1 + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) z.1 -
        X.X (τ z.1) z.1)}
  let F : Set (Ω × ℝ) := {z | (τ z.1 : ℝ) ≤ z.2 ∧ z.1 ∈ A ∧
    ∀ u : ℝ≥0, u ≤ Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
      0 ≤ a + (X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1)}
  have hg : MeasurableSet G := hGrid
  have hf : MeasurableSet F := hFull
  have hI : (∫⁻ z, G.indicator (fun _ => (1 : ℝ≥0∞)) z ∂Qp) =
      (∫⁻ z, F.indicator (fun _ => (1 : ℝ≥0∞)) z ∂Qp) := by
    convert hAccepted using 1
  have hG : (∫⁻ z, G.indicator (fun _ => (1 : ℝ≥0∞)) z ∂Qp) =
      Qp G := lintegral_indicator_one hg
  have hF : (∫⁻ z, F.indicator (fun _ => (1 : ℝ≥0∞)) z ∂Qp) =
      Qp F := lintegral_indicator_one hf
  change Qp G = Qp F
  exact hG.symm.trans (hI.trans hF)
