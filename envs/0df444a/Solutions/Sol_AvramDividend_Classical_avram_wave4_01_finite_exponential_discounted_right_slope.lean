-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_finite_exponential_discounted_right_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:50:09.027467+00:00
-- url     : https://prove2.me/submissions/62098549-2c7f-41c5-a989-af4e8bbc4ea3

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Monoid
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_exponential_discounted_increment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (coeff rate : ι → ℝ) (hrate : ∀ i ∈ s, 0 ≤ rate i)
    (q x : ℝ) :
    Tendsto
      (fun h : ℝ => h⁻¹ *
        (Real.exp (-(q * h)) *
          (∫ ω, ∑ i ∈ s, coeff i *
            Real.exp (rate i * (x + X.X (Real.toNNReal h) ω)) ∂P) -
          ∑ i ∈ s, coeff i * Real.exp (rate i * x)))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (∑ i ∈ s, coeff i * Real.exp (rate i * x) *
        (laplaceExponent X.c X.σ X.ν (rate i) - q))) := by
  classical
  have hlim (z : ℝ) :
      Tendsto (fun h : ℝ => h⁻¹ * (Real.exp (h * z) - 1))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds z) := by
    have hd : HasDerivAt (fun h : ℝ => Real.exp (h * z)) z 0 := by
      simpa [Function.comp_def] using (Real.hasDerivAt_exp (0 * z)).comp 0
        ((hasDerivAt_id (0 : ℝ)).mul_const z)
    simpa [smul_eq_mul] using hd.tendsto_slope_zero_right
  have hsum : Tendsto
      (fun h : ℝ => ∑ i ∈ s, coeff i * Real.exp (rate i * x) *
        (h⁻¹ * (Real.exp (h * (laplaceExponent X.c X.σ X.ν (rate i) - q)) - 1)))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (∑ i ∈ s, coeff i * Real.exp (rate i * x) *
        (laplaceExponent X.c X.σ X.ν (rate i) - q))) := by
    apply tendsto_finset_sum s
    intro i hi
    exact (hlim (laplaceExponent X.c X.σ X.ν (rate i) - q)).const_mul
      (coeff i * Real.exp (rate i * x))
  have hevent : (fun h : ℝ => h⁻¹ *
        (Real.exp (-(q * h)) *
          (∫ ω, ∑ i ∈ s, coeff i *
            Real.exp (rate i * (x + X.X (Real.toNNReal h) ω)) ∂P) -
          ∑ i ∈ s, coeff i * Real.exp (rate i * x))) =ᶠ[
      nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))]
      (fun h : ℝ => ∑ i ∈ s, coeff i * Real.exp (rate i * x) *
        (h⁻¹ * (Real.exp (h * (laplaceExponent X.c X.σ X.ν (rate i) - q)) - 1))) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : 0 ≤ h := le_of_lt hh
    have hcoe : ((Real.toNNReal h : ℝ≥0) : ℝ) = h :=
      Real.coe_toNNReal h hh0
    have hinc := avram_wave4_01_finite_exponential_discounted_increment
      X s coeff rate hrate q (Real.toNNReal h) x
    rw [hcoe] at hinc
    rw [hinc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  exact hsum.congr' hevent.symm
