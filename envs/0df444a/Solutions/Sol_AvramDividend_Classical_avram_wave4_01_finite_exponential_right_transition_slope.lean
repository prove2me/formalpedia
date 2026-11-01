-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_finite_exponential_right_transition_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:16:18.73232+00:00
-- url     : https://prove2.me/submissions/8b9c6440-aa99-4ed0-b144-7fe2a8080bc2

import Mathlib.Topology.Algebra.Monoid
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_right_generator
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
    (coeff rate : ι → ℝ)
    (hrate : ∀ i ∈ s, 0 ≤ rate i) (x : ℝ) : Tendsto
      (fun h : ℝ => h⁻¹ *
        ((∫ ω, ∑ i ∈ s, coeff i *
            Real.exp (rate i * (x + X.X (Real.toNNReal h) ω)) ∂P) -
          ∑ i ∈ s, coeff i * Real.exp (rate i * x)))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (∑ i ∈ s, coeff i *
        X.generator (fun z : ℝ => Real.exp (rate i * z)) x)) := by
  classical
  have hint (r : ℝ) : ∀ i ∈ s, Integrable (fun ω => coeff i * Real.exp (rate i * (x + X.X (Real.toNNReal r) ω))) P := by
    intro i hi
    have h0 : Integrable (fun ω => Real.exp (rate i * X.X (Real.toNNReal r) ω)) P :=
      (X.laplace (Real.toNNReal r) (rate i) (hrate i hi)).1
    have hfun :
        (fun ω => coeff i *
          Real.exp (rate i * (x + X.X (Real.toNNReal r) ω))) =
        (fun ω => (coeff i * Real.exp (rate i * x)) *
          Real.exp (rate i * X.X (Real.toNNReal r) ω)) := by
      funext ω
      rw [mul_add, Real.exp_add]
      ring
    rw [hfun]
    exact h0.const_mul _
  have hlinear (r : ℝ) : (∫ ω, ∑ i ∈ s, coeff i *
          Real.exp (rate i * (x + X.X (Real.toNNReal r) ω)) ∂P) =
        ∑ i ∈ s, coeff i *
          (∫ ω, Real.exp
            (rate i * (x + X.X (Real.toNNReal r) ω)) ∂P) := by
    rw [integral_finset_sum s (hint r)]
    simp only [integral_const_mul, smul_eq_mul]
  have hsum : Tendsto (fun r : ℝ => ∑ i ∈ s, coeff i *
        (r⁻¹ * ((∫ ω, Real.exp
          (rate i * (x + X.X (Real.toNNReal r) ω)) ∂P) -
          Real.exp (rate i * x))))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (∑ i ∈ s, coeff i *
        X.generator (fun z : ℝ => Real.exp (rate i * z)) x)) := by
    apply tendsto_finset_sum s
    intro i hi
    exact (levy_transition_exponential_right_generator X (rate i) x
      (hrate i hi)).const_mul (coeff i)
  have hevent : (fun r : ℝ => r⁻¹ *
        ((∫ ω, ∑ i ∈ s, coeff i *
            Real.exp (rate i * (x + X.X (Real.toNNReal r) ω)) ∂P) -
          ∑ i ∈ s, coeff i * Real.exp (rate i * x))) =ᶠ[
        nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))]
      (fun r : ℝ => ∑ i ∈ s, coeff i *
        (r⁻¹ * ((∫ ω, Real.exp
          (rate i * (x + X.X (Real.toNNReal r) ω)) ∂P) -
          Real.exp (rate i * x)))) := by
    apply Filter.Eventually.of_forall
    intro r
    dsimp only
    rw [hlinear r]
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  exact hsum.congr' hevent.symm
