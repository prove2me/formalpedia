-- Prove2me | solution 1 for AvramDividend.Classical.esscher_bounded_stop_independent_clock_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T23:31:18.36326+00:00
-- url     : https://prove2.me/submissions/5a1a99a5-d08b-4326-8ed6-17e8e4ec0c26

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_map_law
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (B : Set ℝ) (hB : MeasurableSet B)
    (p : ℝ) (hp : 0 < p) (C : Set ℝ) :
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod
       (expMeasure p))
      ((A ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) ×ˢ C) =
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B)) * (expMeasure p) C := by
  have hXu : Measurable (X.X u) := (X.adapted u).mono (𝓕.le u) le_rfl
  have hY : Measurable (fun ω => X.X (τ ω + u) ω - X.X (τ ω) ω) :=
    (measurable_pi_apply u).comp
      (levy_boundedStopping_stoppedFuturePath_measurable X τ hstop H hbound)
  have hlaw := esscher_bounded_stop_future_increment_map_law X θ hθ τ hstop H hbound u T hT A hA
  have := congrArg (fun μ : Measure ℝ => μ B) hlaw
  rw [Measure.map_apply hY hB, Measure.restrict_apply (hY hB), Measure.smul_apply,
    Measure.map_apply hXu hB, smul_eq_mul, Set.inter_comm] at this
  haveI : IsProbabilityMeasure (expMeasure p) := isProbabilityMeasure_expMeasure hp
  haveI : IsProbabilityMeasure (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) :=
    chat04_esscher_weighted_finite_horizon_probability X T θ hθ
  rw [Measure.prod_prod]
  congr 1
