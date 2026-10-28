-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_compensated_increment_centered_memLp_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:11:05.092713+00:00
-- url     : https://prove2.me/submissions/82838154-347b-4fc8-8450-5a291f73b93c

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_exp_memLp_two
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- The centered, cumulant-normalised Lévy exponential increment belongs to L². -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    MemLp (fun ω => Real.exp (-((h : ℝ) * X.ψ θ)) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) - 1) 2 P := by
  have hg := levy_bounded_stopping_increment_exp_memLp_two
    X τ hτ T hbounded h θ hθ
  have hscaled := hg.const_mul (Real.exp (-((h : ℝ) * X.ψ θ)))
  have hone : MemLp (fun _ : Ω => (1 : ℝ)) 2 P :=
    memLp_const (1 : ℝ)
  exact hscaled.sub hone
