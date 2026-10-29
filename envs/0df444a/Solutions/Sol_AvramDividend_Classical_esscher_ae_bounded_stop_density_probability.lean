-- Prove2me | solution 1 for AvramDividend.Classical.esscher_ae_bounded_stop_density_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:55:01.388553+00:00
-- url     : https://prove2.me/submissions/ff1ac3c1-7706-44bb-bf9c-5edbcf77a556

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_density_probability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (haeBound : ∀ᵐ ω ∂P, τ ω ≤ H)
    (T : ℝ≥0) (hT : H + 1 ≤ T) :
    IsProbabilityMeasure (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))) := by
  let σ : Ω → ℝ≥0 := fun ω => min (τ ω) H
  have hσstop : IsStoppingTime 𝓕
      (fun ω => (σ ω : WithTop ℝ≥0)) := by
    simpa only [σ, WithTop.coe_min] using hstop.min_const H
  have hσbound : ∀ ω, σ ω ≤ H := by
    intro ω
    exact min_le_right _ _
  have hDensityEq :
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (θ * X.X (τ ω) ω -
          (τ ω : ℝ) * X.ψ θ)))) =
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (θ * X.X (σ ω) ω -
          (σ ω : ℝ) * X.ψ θ)))) := by
    apply withDensity_congr_ae
    filter_upwards [haeBound] with ω hw
    simp only [σ, min_eq_left hw]
  rw [hDensityEq]
  exact esscher_bounded_stop_density_probability
    X θ hθ σ hσstop H hσbound T hT
