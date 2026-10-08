-- Prove2me | solution 1 for AvramDividend.Classical.generator_const_mul_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T23:27:55.245364+00:00
-- url     : https://prove2.me/submissions/ae5ba1cc-a39d-4669-b34b-67762f1a95ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
The generator in the mission is a linear combination of derivatives
and a compensated jump integral. Multiplication by an arbitrary real
constant preserves its value and maps integrable jump functions to
integrable jump functions, even when the scalar is zero.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (x k : ℝ)
    (hf : X.GeneratorIntegrable f x) :
    X.GeneratorIntegrable (fun z => k * f z) x ∧
      X.generator (fun z => k * f z) x = k * X.generator f x := by
  have hderiv :
      deriv (fun z => k * f z) x = k * deriv f x := by
    simpa only [smul_eq_mul] using
      (deriv_fun_const_smul_field (c := k) (f := f) (x := x))
  have hiter :
      iteratedDeriv 2 (fun z => k * f z) x =
        k * iteratedDeriv 2 f x := by
    simpa only [smul_eq_mul] using
      (iteratedDeriv_fun_const_smul_field (n := 2)
        (c := k) (f := f) (x := x))
  have hint :
      ∀ y : ℝ,
        SpectrallyNegativeLevy.generatorIntegrand
            (fun z => k * f z) x y =
          k * SpectrallyNegativeLevy.generatorIntegrand f x y := by
    intro y
    unfold SpectrallyNegativeLevy.generatorIntegrand
    rw [hderiv]
    ring
  have hint_fun :
      SpectrallyNegativeLevy.generatorIntegrand
          (fun z => k * f z) x =
        (fun y => k * SpectrallyNegativeLevy.generatorIntegrand f x y) :=
    funext hint
  have hscaled : X.GeneratorIntegrable (fun z => k * f z) x := by
    change IntegrableOn
      (SpectrallyNegativeLevy.generatorIntegrand (fun z => k * f z) x)
      (Iio (0 : ℝ)) X.ν
    rw [hint_fun]
    exact hf.const_mul k
  constructor
  · exact hscaled
  · have hintegral :
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand
            (fun z => k * f z) x y ∂X.ν) =
        k * (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand f x y ∂X.ν) := by
      rw [hint_fun]
      rw [integral_const_mul]
    unfold SpectrallyNegativeLevy.generator
    rw [hderiv, hiter, hintegral]
    ring
