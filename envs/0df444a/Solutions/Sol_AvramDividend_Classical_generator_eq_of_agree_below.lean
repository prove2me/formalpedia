-- Prove2me | solution 1 for AvramDividend.Classical.generator_eq_of_agree_below
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T23:16:05.457984+00:00
-- url     : https://prove2.me/submissions/1c788391-8ac2-4f6a-8b63-050806cc4152

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Locality of the spectrally negative generator: only values at and below x
enter the jump term, and the two differential terms are local at x.
-/ 
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (f g : ℝ → ℝ)
    (a x : ℝ) (hx : x < a)
    (hfg : ∀ z : ℝ, z < a → f z = g z) :
    (X.GeneratorIntegrable f x ↔ X.GeneratorIntegrable g x) ∧
      X.generator f x = X.generator g x := by
  have hon : Set.EqOn f g (Iio a) := by
    intro z hz
    exact hfg z hz
  have hvalue : f x = g x := hfg x hx
  have hderiv : deriv f x = deriv g x :=
    (hon.deriv isOpen_Iio) hx
  have hiter : iteratedDeriv 2 f x = iteratedDeriv 2 g x := by
    have h2 :
        iteratedDerivWithin 2 f (Iio a) x =
          iteratedDerivWithin 2 g (Iio a) x :=
      (iteratedDerivWithin_congr (n := 2) hon) hx
    calc
      iteratedDeriv 2 f x =
          iteratedDerivWithin 2 f (Iio a) x :=
        ((iteratedDerivWithin_of_isOpen (f := f) (n := 2) isOpen_Iio) hx).symm
      _ = iteratedDerivWithin 2 g (Iio a) x := h2
      _ = iteratedDeriv 2 g x :=
        (iteratedDerivWithin_of_isOpen (f := g) (n := 2) isOpen_Iio) hx
  have hintegrand :
      Set.EqOn
        (SpectrallyNegativeLevy.generatorIntegrand f x)
        (SpectrallyNegativeLevy.generatorIntegrand g x)
        (Iio (0 : ℝ)) := by
    intro y hy
    have hy0 : y < 0 := hy
    have hxy : x + y < a := by linarith
    simp only [SpectrallyNegativeLevy.generatorIntegrand,
      hfg (x + y) hxy, hvalue, hderiv]
  constructor
  · exact integrableOn_congr_fun hintegrand measurableSet_Iio
  · unfold SpectrallyNegativeLevy.generator
    rw [hiter, hderiv,
      setIntegral_congr_fun measurableSet_Iio hintegrand]
