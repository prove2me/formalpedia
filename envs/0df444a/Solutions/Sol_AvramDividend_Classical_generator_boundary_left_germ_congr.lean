-- Prove2me | solution 1 for AvramDividend.Classical.generator_boundary_left_germ_congr
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T11:11:36.014879+00:00
-- url     : https://prove2.me/submissions/57509ed6-840d-4e38-8da9-e6b027955eb7

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set
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
    (f g : ℝ → ℝ) (a : ℝ)
    (hleft : ∀ z : ℝ, z ≤ a → f z = g z)
    (hder : deriv f a = deriv g a)
    (hsecond : iteratedDeriv 2 f a = iteratedDeriv 2 g a) :
    (X.GeneratorIntegrable f a ↔ X.GeneratorIntegrable g a) ∧
      X.generator f a = X.generator g a := by
  have hfa : f a = g a := hleft a le_rfl
  have hjump : EqOn
      (SpectrallyNegativeLevy.generatorIntegrand f a)
      (SpectrallyNegativeLevy.generatorIntegrand g a)
      (Iio (0 : ℝ)) := by
    intro y hy
    have hy0 : y < 0 := hy
    have hxy : a + y ≤ a := by linarith
    have hfg : f (a + y) = g (a + y) := hleft _ hxy
    simp only [SpectrallyNegativeLevy.generatorIntegrand, hfg, hfa, hder]
  constructor
  · change IntegrableOn
        (SpectrallyNegativeLevy.generatorIntegrand f a)
        (Iio (0 : ℝ)) X.ν ↔
      IntegrableOn (SpectrallyNegativeLevy.generatorIntegrand g a)
        (Iio (0 : ℝ)) X.ν
    exact integrableOn_congr_fun hjump measurableSet_Iio
  · unfold SpectrallyNegativeLevy.generator
    rw [hsecond, hder]
    rw [setIntegral_congr_fun measurableSet_Iio hjump]