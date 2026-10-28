-- Prove2me | solution 2 for AvramDividend.Classical.zero_jump_affine_generator_eq_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:16:05.990759+00:00
-- url     : https://prove2.me/submissions/89c0f10a-db88-46ab-b51b-c49713b80754

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The extended Lévy generator of an affine test payoff is exactly the
    drift coefficient when the Lévy jump measure vanishes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) (x : ℝ) :
    X.GeneratorIntegrable (fun z : ℝ => z - 1) x ∧
      X.generator (fun z : ℝ => z - 1) x = X.c := by
  constructor
  · change IntegrableOn _ (Iio (0 : ℝ)) X.ν
    apply IntegrableOn.of_measure_zero
    simp [hν]
  · simp [SpectrallyNegativeLevy.generator, hν,
      iteratedDeriv_succ, iteratedDeriv_zero]
