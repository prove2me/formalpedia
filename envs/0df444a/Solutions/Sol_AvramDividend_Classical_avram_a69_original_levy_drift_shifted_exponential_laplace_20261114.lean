-- Prove2me | solution 1 for AvramDividend.Classical.avram_a69_original_levy_drift_shifted_exponential_laplace_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:55:55.217205+00:00
-- url     : https://prove2.me/submissions/2af15ef2-57d2-4ec5-bb0c-7ca8fef8b6be

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ d : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp (θ * (X.X t ω - d))) P ∧
    (∫ ω, Real.exp (θ * (X.X t ω - d)) ∂P) =
      Real.exp ((t : ℝ) * X.ψ θ - θ * d) := by
  have hOriginal := X.laplace t θ hθ
  have hPoint (ω : Ω) :
      Real.exp (θ * (X.X t ω - d)) =
        Real.exp (-θ * d) * Real.exp (θ * X.X t ω) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hFun :
      (fun ω => Real.exp (θ * (X.X t ω - d))) =
        (fun ω => Real.exp (-θ * d) * Real.exp (θ * X.X t ω)) :=
    funext hPoint
  constructor
  · rw [hFun]
    exact hOriginal.1.const_mul _
  · rw [hFun, integral_const_mul]
    have hLap :
        (∫ ω, Real.exp (θ * X.X t ω) ∂P) =
          Real.exp ((t : ℝ) * X.ψ θ) := hOriginal.2
    rw [hLap, ← Real.exp_add]
    congr 1
    ring
