-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_finite_exponential_transition_family
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:10:27.253427+00:00
-- url     : https://prove2.me/submissions/9f2698dc-3a8e-4ec5-859e-8bd5aaf0f5c5

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_eigenfunction

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (coeff rate : ι → ℝ)
    (hrate : ∀ i ∈ s, 0 ≤ rate i)
    (t : ℝ≥0) (x : ℝ) :
    (∫ ω, ∑ i ∈ s, coeff i *
        Real.exp (rate i * (x + X.X t ω)) ∂P) =
      ∑ i ∈ s, coeff i *
        (Real.exp (rate i * x) *
          Real.exp ((t : ℝ) *
            laplaceExponent X.c X.σ X.ν (rate i))) := by
  classical
  have hint : ∀ i ∈ s,
      Integrable (fun ω => coeff i *
        Real.exp (rate i * (x + X.X t ω))) P := by
    intro i hi
    have h0 : Integrable
        (fun ω => Real.exp (rate i * X.X t ω)) P :=
      (X.laplace t (rate i) (hrate i hi)).1
    have hfun :
        (fun ω => coeff i * Real.exp (rate i * (x + X.X t ω))) =
        (fun ω => (coeff i * Real.exp (rate i * x)) *
          Real.exp (rate i * X.X t ω)) := by
      funext ω
      rw [mul_add, Real.exp_add]
      ring
    rw [hfun]
    exact h0.const_mul _
  rw [integral_finset_sum s hint]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∫ ω, coeff i * Real.exp (rate i * (x + X.X t ω)) ∂P) =
        coeff i * (∫ ω, Real.exp (rate i * (x + X.X t ω)) ∂P) := by
      simp only [integral_const_mul, smul_eq_mul]
    _ = coeff i * (Real.exp (rate i * x) *
          Real.exp ((t : ℝ) *
            laplaceExponent X.c X.σ X.ν (rate i))) := by
      rw [levy_transition_exponential_eigenfunction X t (rate i)
        (hrate i hi) x]
