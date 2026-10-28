-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_increment_laplace_time_semigroup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:37:09.714988+00:00
-- url     : https://prove2.me/submissions/fcada8cc-9f8f-49b2-aed9-ff35f53c1ab0

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_laplace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- The post-stopping exponential transform multiplies over successive deterministic horizons. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h k : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, Real.exp (θ *
      (X.X (τ ω + (h + k)) ω - X.X (τ ω) ω)) ∂P =
        Real.exp ((h : ℝ) * X.ψ θ) *
          Real.exp ((k : ℝ) * X.ψ θ) := by
  rw [levy_bounded_stopping_increment_laplace
    X τ hτ T hbounded (h + k) θ hθ]
  rw [← Real.exp_add]
  congr 1
  simp only [NNReal.coe_add, add_mul]
