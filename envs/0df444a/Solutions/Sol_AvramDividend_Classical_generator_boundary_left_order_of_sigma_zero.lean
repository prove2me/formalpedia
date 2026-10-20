-- Prove2me | solution 1 for AvramDividend.Classical.generator_boundary_left_order_of_sigma_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T12:47:54.316998+00:00
-- url     : https://prove2.me/submissions/0b2700ed-94a0-4af4-af42-68e7d3797cd4

import Mathlib.Tactic.Linarith
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
    (hσ : X.σ = 0)
    (f g : ℝ → ℝ) (a : ℝ)
    (hle : ∀ z : ℝ, z ≤ a → f z ≤ g z)
    (hat : f a = g a)
    (hder : deriv f a = deriv g a)
    (hf : X.GeneratorIntegrable f a)
    (hg : X.GeneratorIntegrable g a) :
    X.generator f a ≤ X.generator g a := by
  have hjump : ∀ y ∈ Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand f a y ≤
        SpectrallyNegativeLevy.generatorIntegrand g a y := by
    intro y hy
    have hxy : a + y ≤ a := by have := (show y < 0 from hy); linarith
    have hfg : f (a + y) ≤ g (a + y) := hle _ hxy
    unfold SpectrallyNegativeLevy.generatorIntegrand
    rw [hat, hder]
    linarith
  have hjumpint : (∫ y in Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand f a y ∂X.ν) ≤
        ∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand g a y ∂X.ν := by
    exact setIntegral_mono_on hf hg measurableSet_Iio hjump
  simpa [SpectrallyNegativeLevy.generator, hσ, hder] using
    (add_le_add_left hjumpint (X.c * deriv g a))