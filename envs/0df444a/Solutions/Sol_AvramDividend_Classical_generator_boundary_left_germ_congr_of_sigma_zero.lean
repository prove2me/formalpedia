-- Prove2me | solution 1 for AvramDividend.Classical.generator_boundary_left_germ_congr_of_sigma_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T11:16:18.178195+00:00
-- url     : https://prove2.me/submissions/21cdbcdd-3b32-4b61-a643-65320662abcf

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
    (hσ : X.σ = 0)
    (f g : ℝ → ℝ) (a : ℝ)
    (hleft : ∀ z : ℝ, z ≤ a → f z = g z)
    (hder : deriv f a = deriv g a) :
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
    simp [hσ, hder, setIntegral_congr_fun measurableSet_Iio hjump]
