-- Prove2me | solution 1 for AvramDividend.Classical.zero_jump_affine_cutoff_generator_eq_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:31:04.793252+00:00
-- url     : https://prove2.me/submissions/d402e69d-6fe7-4e5b-b518-e19e089772e1

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_affine_cutoff_deriv_eq_one_positive
import Theorems.Thm_AvramDividend_Classical_affine_cutoff_second_deriv_eq_zero_positive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (y : ℝ) (hy : 0 < y) :
    X.GeneratorIntegrable (fun z : ℝ => if z < 0 then 0 else z - 1) y ∧
      X.generator (fun z : ℝ => if z < 0 then 0 else z - 1) y = X.c := by
  have hd := AvramDividend.Classical.affine_cutoff_deriv_eq_one_positive y hy
  have hd2 := AvramDividend.Classical.affine_cutoff_second_deriv_eq_zero_positive y hy
  constructor
  · change IntegrableOn _ (Iio (0 : ℝ)) X.ν
    apply IntegrableOn.of_measure_zero
    simp [hν]
  · simp [SpectrallyNegativeLevy.generator, hν, hd, hd2]
