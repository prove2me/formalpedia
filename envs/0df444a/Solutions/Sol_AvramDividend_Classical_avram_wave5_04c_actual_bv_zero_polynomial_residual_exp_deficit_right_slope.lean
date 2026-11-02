-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_bv_zero_polynomial_residual_exp_deficit_right_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:22:36.456592+00:00
-- url     : https://prove2.me/submissions/fb8b0897-7421-492f-8277-617228a30220

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_finite_signed_exponential_right_slope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

/-! The exact finite exponential-deficit primitive coefficients associated
with a zero-constant polynomial inherit the right slope of the original BV
source residual, with no coupling, process replacement, or new assumptions. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (p : Polynomial ℝ) (hp : Polynomial.eval 0 p = 0) :
    Tendsto
      (fun h : ℝ => ∑ k ∈ p.support.erase 0,
        (p.coeff k / (k : ℝ)) * (h⁻¹ * (1 -
          (∫ ω, Real.exp ((k : ℝ) *
            (-((Real.toNNReal h : ℝ) * X.drift -
              X.X (Real.toNNReal h) ω))) ∂P))))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∑ k ∈ p.support.erase 0,
        (p.coeff k / (k : ℝ)) *
          (∫ y in Iio (0 : ℝ), 1 - Real.exp ((k : ℝ) * y) ∂X.ν))) := by
  apply avram_wave5_04c_actual_bv_residual_finite_signed_exponential_right_slope
    X hBV (p.support.erase 0)
  intro k hk
  have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
  omega
