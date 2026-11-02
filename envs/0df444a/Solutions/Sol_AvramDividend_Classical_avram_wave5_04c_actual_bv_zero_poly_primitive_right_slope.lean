-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_bv_zero_poly_primitive_right_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:44:57.176397+00:00
-- url     : https://prove2.me/submissions/d2497dca-8c5e-4be0-ae64-a3228b3c1839

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_zero_poly_primitive_expectation
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_zero_polynomial_residual_exp_deficit_right_slope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

/-! Original-source right-time generator slope of every exact zero-constant
polynomial primitive, after justified Bochner expectation interchange. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (p : Polynomial ℝ) (hp : Polynomial.eval 0 p = 0) :
    Tendsto
      (fun h : ℝ => h⁻¹ *
        (∫ ω, (∫ r in (0 : ℝ)..
          ((Real.toNNReal h : ℝ) * X.drift -
            X.X (Real.toNNReal h) ω),
          Polynomial.eval (Real.exp (-r)) p) ∂P))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∑ k ∈ p.support.erase 0,
        (p.coeff k / (k : ℝ)) *
          (∫ y in Iio (0 : ℝ), 1 - Real.exp ((k : ℝ) * y) ∂X.ν))) := by
  have hId (h : ℝ) :
      h⁻¹ *
        (∫ ω, (∫ r in (0 : ℝ)..
          ((Real.toNNReal h : ℝ) * X.drift -
            X.X (Real.toNNReal h) ω),
          Polynomial.eval (Real.exp (-r)) p) ∂P) =
      ∑ k ∈ p.support.erase 0,
        (p.coeff k / (k : ℝ)) * (h⁻¹ * (1 -
          (∫ ω, Real.exp ((k : ℝ) *
            (-((Real.toNNReal h : ℝ) * X.drift -
              X.X (Real.toNNReal h) ω))) ∂P))) := by
    rw [avram_wave5_04c_actual_bv_zero_poly_primitive_expectation
      X hBV p hp (Real.toNNReal h)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [mul_neg, neg_mul]
    ring
  have hbase :=
    avram_wave5_04c_actual_bv_zero_polynomial_residual_exp_deficit_right_slope
      X hBV p hp
  exact hbase.congr' (Filter.Eventually.of_forall (fun h => (hId h).symm))
