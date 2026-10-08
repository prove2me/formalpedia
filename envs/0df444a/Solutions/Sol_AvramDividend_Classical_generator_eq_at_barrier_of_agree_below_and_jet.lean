-- Prove2me | solution 1 for AvramDividend.Classical.generator_eq_at_barrier_of_agree_below_and_jet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:26:05.828374+00:00
-- url     : https://prove2.me/submissions/c8fa93e3-d8ec-4ca3-acf9-74d14fd58998

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (f g : ℝ → ℝ) (a : ℝ)
    (hfg : ∀ z : ℝ, z ≤ a → f z = g z)
    (hder : deriv f a = deriv g a)
    (hsecond : iteratedDeriv 2 f a = iteratedDeriv 2 g a) :
    (X.GeneratorIntegrable f a ↔ X.GeneratorIntegrable g a) ∧
      X.generator f a = X.generator g a := by
  have h_eq : EqOn
      (SpectrallyNegativeLevy.generatorIntegrand f a)
      (SpectrallyNegativeLevy.generatorIntegrand g a) (Iio (0 : ℝ)) := by
    intro y hy
    have hy0 : y < 0 := by simpa using hy
    have hza : a + y ≤ a := by linarith
    simp only [SpectrallyNegativeLevy.generatorIntegrand,
      hfg (a + y) hza, hfg a (le_refl a), hder]
  constructor
  · change IntegrableOn
      (SpectrallyNegativeLevy.generatorIntegrand f a) (Iio (0 : ℝ)) X.ν ↔
      IntegrableOn
      (SpectrallyNegativeLevy.generatorIntegrand g a) (Iio (0 : ℝ)) X.ν
    exact integrableOn_congr_fun h_eq measurableSet_Iio
  · have h_integral :
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand f a y ∂X.ν) =
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand g a y ∂X.ν) :=
      setIntegral_congr_fun measurableSet_Iio h_eq
    simp only [SpectrallyNegativeLevy.generator,
      hsecond, hder, h_integral]
