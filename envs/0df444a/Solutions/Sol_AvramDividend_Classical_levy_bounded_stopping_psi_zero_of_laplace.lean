-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_psi_zero_of_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:42:17.190026+00:00
-- url     : https://prove2.me/submissions/5131f772-ab06-40b9-99dd-3f81dd559da8

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_laplace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- Normalisation of the Lévy Laplace exponent at zero from the stopped transform. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T) :
    X.ψ 0 = 0 := by
  have hLaplace := levy_bounded_stopping_increment_laplace
    X τ hτ T hbounded 1 0 (le_refl 0)
  have hExp : Real.exp (X.ψ 0) = 1 := by
    simpa using hLaplace.symm
  have hEq : Real.exp (X.ψ 0) = Real.exp 0 := by
    simpa using hExp
  exact Real.exp_injective hEq
