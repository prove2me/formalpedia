-- Prove2me | solution 1 for AvramDividend.Classical.scaledW_generator_harmonic_of_scale_harmonic_at_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T13:31:42.807058+00:00
-- url     : https://prove2.me/submissions/2f1ea0f2-dcf5-4123-a245-ce701092cf3e

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_levy_generator_const_mul
import Theorems.Thm_AvramDividend_Classical_levy_generatorIntegrable_const_mul
import Mathlib.MeasureTheory.MeasurableSpace.Defs

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
    (q : ℝ) (W : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hdom : X.GeneratorIntegrable W a)
    (hharm : X.generator W a - q * W a = 0) :
    X.GeneratorIntegrable
      (fun z : ℝ => divE (W z) (scaleDeriv W a)) a ∧
      X.generator
        (fun z : ℝ => divE (W z) (scaleDeriv W a)) a -
        q * divE (W a) (scaleDeriv W a) = 0 := by
  let k : ℝ := (deriv W a)⁻¹
  have hfun :
      (fun z : ℝ => divE (W z) (scaleDeriv W a)) =
        (fun z : ℝ => k * W z) := by
    funext z
    have ha0 : a ≠ 0 := ne_of_gt ha
    simp [divE, scaleDeriv, ha0, k, div_eq_mul_inv, mul_comm]
  have hvalue : divE (W a) (scaleDeriv W a) = k * W a :=
    congrFun hfun a
  constructor
  · rw [hfun]
    exact levy_generatorIntegrable_const_mul X W k a hdom
  · rw [hfun, hvalue]
    rw [levy_generator_const_mul X W k a]
    calc
      k * X.generator W a - q * (k * W a) =
          k * (X.generator W a - q * W a) := by ring
      _ = 0 := by rw [hharm]; ring
