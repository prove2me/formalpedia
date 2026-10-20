-- Prove2me | solution 1 for AvramDividend.Classical.levy_generator_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T13:22:24.586861+00:00
-- url     : https://prove2.me/submissions/57d0d0fc-0069-4423-bf49-c00c560897a4

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

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
    (f : ℝ → ℝ) (k x : ℝ) :
    X.generator (fun z : ℝ => k * f z) x =
      k * X.generator f x := by
  have hder : deriv (fun z : ℝ => k * f z) x = k * deriv f x :=
    deriv_const_mul_field k
  have hsecond :
      iteratedDeriv 2 (fun z : ℝ => k * f z) x =
        k * iteratedDeriv 2 f x :=
    iteratedDeriv_const_mul_field k f
  have hpoint : ∀ y : ℝ,
      SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => k * f z) x y =
        k * SpectrallyNegativeLevy.generatorIntegrand f x y := by
    intro y
    unfold SpectrallyNegativeLevy.generatorIntegrand
    rw [hder]
    ring
  have hjump :
      (∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => k * f z) x y ∂X.ν) =
        k * ∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand f x y ∂X.ν := by
    simp_rw [hpoint]
    rw [integral_const_mul]
  unfold SpectrallyNegativeLevy.generator
  rw [hsecond, hder, hjump]
  ring
