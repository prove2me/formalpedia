-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_finite_exponential_discounted_generator_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:07:38.44293+00:00
-- url     : https://prove2.me/submissions/edf61afa-3224-4a25-b495-f220f24a35d4

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Monoid
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_exponential_generator_linear
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_exponential_discounted_right_slope
import Theorems.Thm_AvramDividend_Classical_generator_exp_eq_psi
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open Filter MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The genuine discounted Lévy transition semigroup has the exact full
generator as its right derivative on every finite signed exponential test. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (coeff rate : ι → ℝ) (hrate : ∀ i ∈ s, 0 ≤ rate i)
    (q x : ℝ) :
    X.GeneratorIntegrable
      (fun z : ℝ => ∑ i ∈ s, coeff i * Real.exp (rate i * z)) x ∧
    Tendsto
      (fun h : ℝ => h⁻¹ *
        (Real.exp (-(q * h)) *
          (∫ ω, ∑ i ∈ s, coeff i *
            Real.exp (rate i * (x + X.X (Real.toNNReal h) ω)) ∂P) -
          ∑ i ∈ s, coeff i * Real.exp (rate i * x)))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (X.generator
        (fun z : ℝ => ∑ i ∈ s, coeff i * Real.exp (rate i * z)) x -
        q * (∑ i ∈ s, coeff i * Real.exp (rate i * x)))) := by
  obtain ⟨hint, hgen⟩ :=
    avram_wave4_01_finite_exponential_generator_linear X s coeff rate hrate x
  refine ⟨hint, ?_⟩
  have hslope :=
    avram_wave4_01_finite_exponential_discounted_right_slope
      X s coeff rate hrate q x
  have h_rhs :
      (∑ i ∈ s, coeff i * Real.exp (rate i * x) *
        (laplaceExponent X.c X.σ X.ν (rate i) - q)) =
      X.generator
        (fun z : ℝ => ∑ i ∈ s, coeff i * Real.exp (rate i * z)) x -
      q * (∑ i ∈ s, coeff i * Real.exp (rate i * x)) := by
    calc
      _ = ∑ i ∈ s,
          (coeff i *
              X.generator (fun z : ℝ => Real.exp (rate i * z)) x -
            q * (coeff i * Real.exp (rate i * x))) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [generator_exp_eq_psi]
              change coeff i * Real.exp (rate i * x) *
                    (laplaceExponent X.c X.σ X.ν (rate i) - q) =
                coeff i *
                    (Real.exp (rate i * x) *
                      laplaceExponent X.c X.σ X.ν (rate i)) -
                  q * (coeff i * Real.exp (rate i * x))
              ring
      _ = (∑ i ∈ s, coeff i *
            X.generator (fun z : ℝ => Real.exp (rate i * z)) x) -
          q * (∑ i ∈ s, coeff i * Real.exp (rate i * x)) := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = _ := by rw [hgen]
  rw [← h_rhs]
  exact hslope
