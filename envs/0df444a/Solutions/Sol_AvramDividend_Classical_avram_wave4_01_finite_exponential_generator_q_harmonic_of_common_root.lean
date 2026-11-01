-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_finite_exponential_generator_q_harmonic_of_common_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:39:11.187325+00:00
-- url     : https://prove2.me/submissions/ef5684ad-9b19-4171-863b-179656d16201

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_exponential_generator_linear
import Theorems.Thm_AvramDividend_Classical_generator_exp_eq_psi
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Every finite signed combination of true q-eigenexponentials lies in
the actual compensated Lévy generator domain and is pointwise q-harmonic. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (coeff rate : ι → ℝ) (hrate : ∀ i ∈ s, 0 ≤ rate i)
    (q x : ℝ) (hroot : ∀ i ∈ s, X.ψ (rate i) = q) :
    X.GeneratorIntegrable
      (fun z : ℝ => ∑ i ∈ s, coeff i * Real.exp (rate i * z)) x ∧
    X.generator
      (fun z : ℝ => ∑ i ∈ s, coeff i * Real.exp (rate i * z)) x -
        q * (∑ i ∈ s, coeff i * Real.exp (rate i * x)) = 0 := by
  obtain ⟨hint, hlinear⟩ :=
    avram_wave4_01_finite_exponential_generator_linear
      X s coeff rate hrate x
  refine ⟨hint, ?_⟩
  rw [hlinear]
  simp_rw [generator_exp_eq_psi]
  have hsum :
      (∑ i ∈ s, coeff i *
        (Real.exp (rate i * x) * X.ψ (rate i))) =
        q * (∑ i ∈ s, coeff i * Real.exp (rate i * x)) := by
    calc
      _ = ∑ i ∈ s, q *
            (coeff i * Real.exp (rate i * x)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hroot i hi]
            ring
      _ = _ := by rw [Finset.mul_sum]
  rw [hsum]
  ring
