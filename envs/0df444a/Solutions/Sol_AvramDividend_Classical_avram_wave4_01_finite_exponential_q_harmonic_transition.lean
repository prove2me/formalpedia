-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_finite_exponential_q_harmonic_transition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:32:46.381587+00:00
-- url     : https://prove2.me/submissions/9ee6f9ba-b6c9-46b8-b161-bee7a53b4f3a

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_exponential_discounted_increment

open MeasureTheory Set
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
    (q : ℝ)
    (hroot : ∀ i ∈ s,
      laplaceExponent X.c X.σ X.ν (rate i) = q)
    (t : ℝ≥0) (x : ℝ) :
    Real.exp (-(q * (t : ℝ))) *
      (∫ ω, ∑ i ∈ s, coeff i *
        Real.exp (rate i * (x + X.X t ω)) ∂P) =
      ∑ i ∈ s, coeff i * Real.exp (rate i * x) := by
  classical
  have hinc := avram_wave4_01_finite_exponential_discounted_increment
    X s coeff rate hrate q t x
  have hzero :
      (∑ i ∈ s, coeff i * Real.exp (rate i * x) *
        (Real.exp ((t : ℝ) *
          (laplaceExponent X.c X.σ X.ν (rate i) - q)) - 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hroot i hi]
    simp
  rw [hzero] at hinc
  exact sub_eq_zero.mp hinc
