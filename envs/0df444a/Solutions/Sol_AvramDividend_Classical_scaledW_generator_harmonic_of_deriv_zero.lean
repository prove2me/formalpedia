-- Prove2me | solution 1 for AvramDividend.Classical.scaledW_generator_harmonic_of_deriv_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T14:22:52.526396+00:00
-- url     : https://prove2.me/submissions/c9ce2e25-fe77-49e7-aa19-d55b40ba1984

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

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
    (q : ℝ) (W : ℝ → ℝ) (a : ℝ)
    (ha : 0 < a) (hder : deriv W a = 0) :
    X.GeneratorIntegrable
      (fun z : ℝ => divE (W z) (scaleDeriv W a)) a ∧
      X.generator
        (fun z : ℝ => divE (W z) (scaleDeriv W a)) a -
        q * divE (W a) (scaleDeriv W a) = 0 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hf :
      (fun z : ℝ => divE (W z) (scaleDeriv W a)) =
        (fun _ : ℝ => (0 : ℝ)) := by
    funext z
    simp [divE, scaleDeriv, ha0, hder]
  have hzero : (SpectrallyNegativeLevy.generatorIntegrand
        (fun _ : ℝ => (0 : ℝ)) a) =
        (fun _ : ℝ => (0 : ℝ)) := by
    funext y
    simp [SpectrallyNegativeLevy.generatorIntegrand]
  constructor
  · rw [hf]
    change IntegrableOn
      (SpectrallyNegativeLevy.generatorIntegrand
        (fun _ : ℝ => (0 : ℝ)) a)
      (Iio (0 : ℝ)) X.ν
    rw [hzero]
    exact integrableOn_zero
  · rw [hf]
    have hv0 : divE (W a) (scaleDeriv W a) = 0 := by
      simp [divE, scaleDeriv, ha0, hder]
    rw [hv0]
    simp [SpectrallyNegativeLevy.generator,
      SpectrallyNegativeLevy.generatorIntegrand,
      iteratedDeriv_const]
