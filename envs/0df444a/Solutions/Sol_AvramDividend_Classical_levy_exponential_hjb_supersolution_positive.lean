-- Prove2me | solution 1 for AvramDividend.Classical.levy_exponential_hjb_supersolution_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:01:47.526626+00:00
-- url     : https://prove2.me/submissions/ccd4269b-ffe6-4a34-afb6-76c36a78b3a3

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_generator_exp_eq_psi
import Mathlib.MeasureTheory.MeasurableSpace.Defs

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
    (θ q x : ℝ) (hθ : 1 ≤ θ) (hx : 0 ≤ x)
    (hψ : X.ψ θ ≤ q) :
    X.generator (fun z : ℝ => Real.exp (θ * z)) x ≤
        q * Real.exp (θ * x) ∧
      1 ≤ deriv (fun z : ℝ => Real.exp (θ * z)) x := by
  have hθ0 : 0 ≤ θ := by linarith
  have hθx : 0 ≤ θ * x := mul_nonneg hθ0 hx
  have he : 1 ≤ Real.exp (θ * x) := by
    have h := Real.add_one_le_exp (θ * x)
    linarith
  constructor
  · calc
      X.generator (fun z : ℝ => Real.exp (θ * z)) x =
          Real.exp (θ * x) * X.ψ θ := generator_exp_eq_psi X θ x
      _ ≤ Real.exp (θ * x) * q :=
          mul_le_mul_of_nonneg_left hψ (Real.exp_nonneg _)
      _ = q * Real.exp (θ * x) := mul_comm _ _
  · have hderiv :
        deriv (fun z : ℝ => Real.exp (θ * z)) x =
          θ * Real.exp (θ * x) := by
      have h := congrFun (iteratedDeriv_exp_const_mul 1 θ) x
      simpa using h
    rw [hderiv]
    nlinarith [mul_nonneg (sub_nonneg.mpr hθ) (sub_nonneg.mpr he)]
