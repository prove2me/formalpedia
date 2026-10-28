-- Prove2me | solution 1 for AvramDividend.Classical.esscher_terminal_independent_clock_increment_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T15:49:51.241999+00:00
-- url     : https://prove2.me/submissions/4c01f480-d47e-42ce-bc26-ae691f0f0139

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_cylinder_factorization
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Under a fixed-terminal tilted path law, the independent exponential clock
factorises from both the observed past and the stationary future increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s u T : ℝ≥0) (hT : s + u ≤ T)
    (p : ℝ) (hp : 0 < p)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (C : Set ℝ) :
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod
        (expMeasure p))
      ((A ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B) ×ˢ C) =
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B)) * (expMeasure p) C := by
  haveI : IsProbabilityMeasure (expMeasure p) :=
    isProbabilityMeasure_expMeasure hp
  rw [Measure.prod_prod]
  rw [esscher_terminal_increment_cylinder_factorization
    X θ hθ s u T hT A hA B hB]
