-- Prove2me | solution 1 for AvramDividend.Classical.levy_compensated_exponential_expectation_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:33:27.291282+00:00
-- url     : https://prove2.me/submissions/f9359798-0356-4d9b-9f17-66d4e2578243

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ) ∂P) = 1 := by
  let a : ℝ := (t : ℝ) * X.ψ θ
  have hLap : (∫ ω, Real.exp (θ * X.X t ω) ∂P) =
      Real.exp a := by
    simpa only [a, SpectrallyNegativeLevy.ψ] using (X.laplace t θ hθ).2
  change (∫ ω, Real.exp (θ * X.X t ω - a) ∂P) = 1
  calc
    (∫ ω, Real.exp (θ * X.X t ω - a) ∂P) =
        ∫ ω, Real.exp (θ * X.X t ω) * Real.exp (-a) ∂P := by
          congr 1
          funext ω
          simp only [Real.exp_sub, Real.exp_neg, div_eq_mul_inv]
    _ = (∫ ω, Real.exp (θ * X.X t ω) ∂P) * Real.exp (-a) := by
          rw [integral_mul_const]
    _ = 1 := by
          rw [hLap, ← Real.exp_add]
          simp
