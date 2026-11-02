-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_finite_signed_exponential_right_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:01:22.838216+00:00
-- url     : https://prove2.me/submissions/7cf82952-0f55-4d22-8bec-12454895be44

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_exponential_test_right_slope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (coeff : ℕ → ℝ) :
    Tendsto
      (fun h : ℝ => ∑ n ∈ s, coeff n * (h⁻¹ * (1 -
        (∫ ω, Real.exp ((n : ℝ) *
          (-((Real.toNNReal h : ℝ) * X.drift -
            X.X (Real.toNNReal h) ω))) ∂P))))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∑ n ∈ s, coeff n *
        (∫ y in Iio (0 : ℝ), 1 - Real.exp ((n : ℝ) * y) ∂X.ν))) := by
  apply tendsto_finset_sum s
  intro n hn
  exact (avram_wave5_04c_actual_bv_residual_exponential_test_right_slope
    X hBV n (hs n hn)).const_mul (coeff n)
