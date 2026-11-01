-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_finite_exponential_discounted_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:21:03.276017+00:00
-- url     : https://prove2.me/submissions/a630e533-4ac3-4d61-90a5-73f30bfd1e50

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_exponential_transition_family

open Filter MeasureTheory Set
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
    (coeff rate : ι → ℝ) (hrate : ∀ i ∈ s, 0 ≤ rate i)
    (q : ℝ) (t : ℝ≥0) (x : ℝ) :
    Real.exp (-(q * (t : ℝ))) *
      (∫ ω, ∑ i ∈ s, coeff i *
        Real.exp (rate i * (x + X.X t ω)) ∂P) -
      ∑ i ∈ s, coeff i * Real.exp (rate i * x) =
    ∑ i ∈ s, coeff i * Real.exp (rate i * x) *
      (Real.exp ((t : ℝ) *
        (laplaceExponent X.c X.σ X.ν (rate i) - q)) - 1) := by
  classical
  rw [avram_wave4_01_finite_exponential_transition_family
    X s coeff rate hrate t x]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hexp :
      Real.exp (-(q * (t : ℝ))) *
        Real.exp ((t : ℝ) *
          laplaceExponent X.c X.σ X.ν (rate i)) =
      Real.exp ((t : ℝ) *
        (laplaceExponent X.c X.σ X.ν (rate i) - q)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (-(q * (t : ℝ))) *
      (coeff i * (Real.exp (rate i * x) *
        Real.exp ((t : ℝ) *
          laplaceExponent X.c X.σ X.ν (rate i)))) -
      coeff i * Real.exp (rate i * x) =
        coeff i * Real.exp (rate i * x) *
          (Real.exp (-(q * (t : ℝ))) *
            Real.exp ((t : ℝ) *
              laplaceExponent X.c X.σ X.ν (rate i)) - 1) := by
      ring
    _ = coeff i * Real.exp (rate i * x) *
          (Real.exp ((t : ℝ) *
            (laplaceExponent X.c X.σ X.ν (rate i) - q)) - 1) := by
      rw [hexp]
