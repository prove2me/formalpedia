-- Prove2me | solution 1 for AvramDividend.Classical.exponential_generator_discount_supersolution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:36:26.623411+00:00
-- url     : https://prove2.me/submissions/15d9abc0-895d-4054-90ca-8a2c2c0c3d41

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_generator_exp_eq_psi

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ q x : ℝ) (hψ : X.ψ θ ≤ q) :
    X.generator (fun y : ℝ => Real.exp (θ * y)) x -
      q * Real.exp (θ * x) ≤ 0 := by
  rw [generator_exp_eq_psi]
  calc
    Real.exp (θ * x) * X.ψ θ - q * Real.exp (θ * x) =
        Real.exp (θ * x) * (X.ψ θ - q) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
      (Real.exp_pos _).le (sub_nonpos.mpr hψ)
