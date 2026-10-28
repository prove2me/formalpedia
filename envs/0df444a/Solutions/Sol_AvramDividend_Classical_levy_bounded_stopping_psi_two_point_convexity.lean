-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_psi_two_point_convexity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:26:04.700163+00:00
-- url     : https://prove2.me/submissions/ee102e10-a555-4f41-a462-6d6e5c4577bd

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_exact_variance
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- The Lévy cumulant obeys its two-point convexity bound via stopped-moment variance. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (hh : 0 < h) (θ : ℝ) (hθ : 0 ≤ θ) :
    2 * X.ψ θ ≤ X.ψ (2 * θ) := by
  have hv := levy_bounded_stopping_compensated_increment_exact_variance
    X τ hτ T hbounded h θ hθ
  have hnonneg : (0 : ℝ) ≤ ∫ ω,
      (Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ θ) - 1) ^ 2 ∂P := by
    apply integral_nonneg
    intro ω
    exact sq_nonneg _
  rw [hv] at hnonneg
  have hExp : Real.exp 0 ≤
      Real.exp ((h : ℝ) * (X.ψ (2 * θ) - 2 * X.ψ θ)) := by
    rw [Real.exp_zero]
    linarith
  have harg : 0 ≤ (h : ℝ) * (X.ψ (2 * θ) - 2 * X.ψ θ) :=
    Real.exp_le_exp.mp hExp
  have hhpos : 0 < (h : ℝ) := by exact_mod_cast hh
  by_contra hn
  have hneg : X.ψ (2 * θ) - 2 * X.ψ θ < 0 := by linarith
  have hcontr := mul_neg_of_pos_of_neg hhpos hneg
  linarith
