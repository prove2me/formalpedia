-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_finite_exponential_test_small_time_source_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:50:11.846532+00:00
-- url     : https://prove2.me/submissions/a32d2831-bf74-49e3-8441-9824d5a46a84

import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_exponential_right_transition_slope
import Theorems.Thm_AvramDividend_Classical_generator_exp_eq_psi

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Genuine original-process Laplace small-time derivative on finite exponential tests. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (coeff rate : ι → ℝ)
    (hrate : ∀ i ∈ I, 0 ≤ rate i) :
    Tendsto
      (fun h : ℝ =>
        ((∫ ω, ∑ i ∈ I, coeff i *
          Real.exp (rate i * X.X (Real.toNNReal h) ω) ∂P) -
          ∑ i ∈ I, coeff i) / h)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∑ i ∈ I, coeff i *
        laplaceExponent X.c X.σ X.ν (rate i))) := by
  classical
  have hGen :
      (∑ i ∈ I, coeff i *
        X.generator (fun z : ℝ => Real.exp (rate i * z)) 0) =
      ∑ i ∈ I, coeff i *
        laplaceExponent X.c X.σ X.ν (rate i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [generator_exp_eq_psi]
    simp [SpectrallyNegativeLevy.ψ]
  have hSource :=
    avram_wave4_01_finite_exponential_right_transition_slope
      X I coeff rate hrate 0
  rw [hGen] at hSource
  have hLeft :
      (fun h : ℝ =>
        ((∫ ω, ∑ i ∈ I, coeff i *
          Real.exp (rate i * X.X (Real.toNNReal h) ω) ∂P) -
          ∑ i ∈ I, coeff i) / h) =
      (fun h : ℝ => h⁻¹ *
        ((∫ ω, ∑ i ∈ I, coeff i *
          Real.exp (rate i * X.X (Real.toNNReal h) ω) ∂P) -
          ∑ i ∈ I, coeff i)) := by
    funext h
    rw [div_eq_mul_inv]
    ring
  rw [hLeft]
  simpa only [zero_add, mul_zero, Real.exp_zero, mul_one] using hSource
