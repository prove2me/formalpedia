-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_drift_exponent_gap_tendsto_intensity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:27:11.048769+00:00
-- url     : https://prove2.me/submissions/790a27b2-8867-40dd-843d-0608c351a4f4

import Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_finite_jump_rearrangement
import Theorems.Thm_AvramDividend_Classical_finite_negative_jump_exp_integral_tendsto_zero_nat
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The BV drift-exponent deficit tends to the finite negative-jump intensity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    Tendsto
      (fun n : ℕ => X.drift * (n : ℝ) - X.ψ (n : ℝ))
      atTop (𝓝 ((X.ν (Iio (0 : ℝ))).toReal)) := by
  have hlimit := finite_negative_jump_exp_integral_tendsto_zero_nat X.ν hFinite
  have hsub : Tendsto
      (fun n : ℕ => (X.ν (Iio (0 : ℝ))).toReal -
        ∫ y in Iio (0 : ℝ), Real.exp ((n : ℝ) * y) ∂X.ν)
      atTop (𝓝 ((X.ν (Iio (0 : ℝ))).toReal - 0)) :=
    tendsto_const_nhds.sub hlimit
  have heq : (fun n : ℕ => X.drift * (n : ℝ) - X.ψ (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => (X.ν (Iio (0 : ℝ))).toReal -
        ∫ y in Iio (0 : ℝ), Real.exp ((n : ℝ) * y) ∂X.ν) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [bv_laplace_exponent_finite_jump_rearrangement
      X hBV (n : ℝ) hn1 hFinite]
    ring
  simpa using hsub.congr' heq.symm
