-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_exponential_test_right_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:57:26.332562+00:00
-- url     : https://prove2.me/submissions/45354bc3-1bfe-4553-abcb-d13c4efd800a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_deficit_laplace_nat
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_scalar_exponential_deficit_right_slope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (n : ℕ) (hn : 1 ≤ n) :
    Tendsto
      (fun h : ℝ => h⁻¹ * (1 -
        (∫ ω, Real.exp ((n : ℝ) *
          (-((Real.toNNReal h : ℝ) * X.drift -
            X.X (Real.toNNReal h) ω))) ∂P)))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ y in Iio (0 : ℝ),
         (1 - Real.exp ((n : ℝ) * y)) ∂X.ν)) := by
  let A : ℝ := ∫ y in Iio (0 : ℝ),
         (1 - Real.exp ((n : ℝ) * y)) ∂X.ν
  have ht (h : ℝ) :
      (∫ ω, Real.exp ((n : ℝ) *
        (-((Real.toNNReal h : ℝ) * X.drift -
          X.X (Real.toNNReal h) ω))) ∂P) =
        Real.exp (-((Real.toNNReal h : ℝ) * A)) := by
    simpa only [A] using
      bv_actual_levy_drift_deficit_laplace_nat
        X hBV (Real.toNNReal h) n hn
  have heq :
      (fun h : ℝ => h⁻¹ * (1 -
        (∫ ω, Real.exp ((n : ℝ) *
          (-((Real.toNNReal h : ℝ) * X.drift -
            X.X (Real.toNNReal h) ω))) ∂P))) =ᶠ[nhdsWithin (0 : ℝ) (Ioi 0)]
      (fun h : ℝ => h⁻¹ * (1 - Real.exp (-(h * A)))) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [ht h]
    simp only [Real.coe_toNNReal h (le_of_lt hh)]
  have hlim := avram_wave5_04c_scalar_exponential_deficit_right_slope A
  change Tendsto _ _ (nhds A)
  exact hlim.congr' heq.symm
