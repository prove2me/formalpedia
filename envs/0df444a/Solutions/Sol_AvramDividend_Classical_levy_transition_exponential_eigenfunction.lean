-- Prove2me | solution 1 for AvramDividend.Classical.levy_transition_exponential_eigenfunction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T22:07:20.714408+00:00
-- url     : https://prove2.me/submissions/00837569-d1d8-4085-ada5-d9e82a1ecd32

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) :
    (∫ ω, Real.exp (θ * (x + X.X t ω)) ∂P) =
      Real.exp (θ * x) *
        Real.exp ((t : ℝ) * laplaceExponent X.c X.σ X.ν θ) := by
  have hLap := (X.laplace t θ hθ).2
  have hpath (ω : Ω) :
      Real.exp (θ * (x + X.X t ω)) =
        Real.exp (θ * x) * Real.exp (θ * X.X t ω) := by
    rw [mul_add, Real.exp_add]
  calc
    (∫ ω, Real.exp (θ * (x + X.X t ω)) ∂P) =
        ∫ ω, Real.exp (θ * x) *
          Real.exp (θ * X.X t ω) ∂P := by
          congr 1
          funext ω
          exact hpath ω
    _ = Real.exp (θ * x) *
          (∫ ω, Real.exp (θ * X.X t ω) ∂P) := by
          rw [integral_const_mul]
    _ = Real.exp (θ * x) *
          Real.exp ((t : ℝ) * laplaceExponent X.c X.σ X.ν θ) := by
          rw [hLap]
