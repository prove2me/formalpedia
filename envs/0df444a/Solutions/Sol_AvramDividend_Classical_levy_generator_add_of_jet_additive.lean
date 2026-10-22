-- Prove2me | solution 1 for AvramDividend.Classical.levy_generator_add_of_jet_additive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:29:35.121398+00:00
-- url     : https://prove2.me/submissions/63cbe146-b4b2-4d97-8824-78b20984911f

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
open AvramDividend.Classical.SpectrallyNegativeLevy

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f g : ℝ → ℝ) (x : ℝ)
    (hf : X.GeneratorIntegrable f x)
    (hg : X.GeneratorIntegrable g x)
    (hfirst :
      deriv (fun z => f z + g z) x = deriv f x + deriv g x)
    (hsecond :
      iteratedDeriv 2 (fun z => f z + g z) x =
        iteratedDeriv 2 f x + iteratedDeriv 2 g x) :
    X.GeneratorIntegrable (fun z => f z + g z) x ∧
      X.generator (fun z => f z + g z) x =
        X.generator f x + X.generator g x := by
  have hpoint (y : ℝ) :
      generatorIntegrand (fun z => f z + g z) x y =
        generatorIntegrand f x y + generatorIntegrand g x y := by
    simp only [generatorIntegrand, hfirst]
    ring
  have hInt :
      X.GeneratorIntegrable (fun z => f z + g z) x := by
    change IntegrableOn
      (generatorIntegrand (fun z => f z + g z) x)
      (Iio 0) X.ν
    have hsum : IntegrableOn
        (fun y => generatorIntegrand f x y +
          generatorIntegrand g x y)
        (Iio 0) X.ν :=
      hf.add hg
    have heq :
        generatorIntegrand (fun z => f z + g z) x =
          (fun y => generatorIntegrand f x y + generatorIntegrand g x y) := by
      funext y
      exact hpoint y
    rw [heq]
    exact hsum
  have hint :
      (∫ y in Iio (0 : ℝ),
        generatorIntegrand (fun z => f z + g z) x y ∂X.ν) =
        (∫ y in Iio (0 : ℝ), generatorIntegrand f x y ∂X.ν) +
          (∫ y in Iio (0 : ℝ), generatorIntegrand g x y ∂X.ν) := by
    simp_rw [hpoint]
    exact integral_add hf hg
  refine ⟨hInt, ?_⟩
  unfold SpectrallyNegativeLevy.generator
  rw [hfirst, hsecond, hint]
  ring
