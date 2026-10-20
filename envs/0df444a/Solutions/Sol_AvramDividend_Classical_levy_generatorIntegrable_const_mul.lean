-- Prove2me | solution 1 for AvramDividend.Classical.levy_generatorIntegrable_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T13:26:44.100131+00:00
-- url     : https://prove2.me/submissions/85545de7-8750-4e99-9ad4-1d519489317a

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (k x : ℝ)
    (hf : X.GeneratorIntegrable f x) :
    X.GeneratorIntegrable (fun z : ℝ => k * f z) x := by
  have hpoint : ∀ y : ℝ,
      SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => k * f z) x y =
        k * SpectrallyNegativeLevy.generatorIntegrand f x y := by
    intro y
    unfold SpectrallyNegativeLevy.generatorIntegrand
    rw [deriv_const_mul_field]
    ring
  have heq :
      (fun y : ℝ =>
        SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => k * f z) x y) =
        (fun y : ℝ => k * SpectrallyNegativeLevy.generatorIntegrand f x y) := by
    funext y
    exact hpoint y
  change Integrable
    (fun y : ℝ =>
      SpectrallyNegativeLevy.generatorIntegrand
        (fun z : ℝ => k * f z) x y)
    (X.ν.restrict (Iio (0 : ℝ)))
  rw [heq]
  exact hf.const_mul k
