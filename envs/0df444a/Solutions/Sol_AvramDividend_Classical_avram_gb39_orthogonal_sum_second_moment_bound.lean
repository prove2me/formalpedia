-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb39_orthogonal_sum_second_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:14:26.40029+00:00
-- url     : https://prove2.me/submissions/84af7355-c44c-4b16-9b82-ddb691415d53

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped BigOperators

/-- Pairwise zero covariance deletes all off-diagonal terms of a finite
    second-moment expansion. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (s : Finset ℕ) (U : ℕ → Ω → ℝ) (K : ℝ)
    (hdiag : ∀ i ∈ s, Integrable (fun ω => (U i ω) ^ 2) P ∧
      (∫ ω, (U i ω) ^ 2 ∂P) ≤ K)
    (hoff : ∀ i ∈ s, ∀ r ∈ s, i ≠ r →
      Integrable (fun ω => U i ω * U r ω) P ∧
      (∫ ω, U i ω * U r ω ∂P) = 0) :
    Integrable (fun ω => ((∑ i ∈ s, U i ω) ^ 2)) P ∧
      (∫ ω, (∑ i ∈ s, U i ω) ^ 2 ∂P) ≤ (s.card : ℝ) * K := by
  classical
  have hp (i : ℕ) (hi : i ∈ s) (r : ℕ) (hr : r ∈ s) :
      Integrable (fun ω => U i ω * U r ω) P := by
    by_cases hir : i = r
    · subst r
      simpa only [pow_two] using (hdiag i hi).1
    · exact (hoff i hi r hr hir).1
  have hrow (i : ℕ) (hi : i ∈ s) :
      Integrable (fun ω => ∑ r ∈ s, U i ω * U r ω) P := by
    exact integrable_finset_sum s (fun r hr => hp i hi r hr)
  have hdouble :
      Integrable (fun ω => ∑ i ∈ s, ∑ r ∈ s, U i ω * U r ω) P := by
    exact integrable_finset_sum s (fun i hi => hrow i hi)
  have hsq (ω : Ω) :
      (∑ i ∈ s, U i ω) ^ 2 =
        ∑ i ∈ s, ∑ r ∈ s, U i ω * U r ω := by
    rw [pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
  have hrowIntegral (i : ℕ) (hi : i ∈ s) :
      (∫ ω, ∑ r ∈ s, U i ω * U r ω ∂P) =
        ∑ r ∈ s, ∫ ω, U i ω * U r ω ∂P := by
    exact integral_finsetSum s (fun r hr => hp i hi r hr)
  have hrowZero (i : ℕ) (hi : i ∈ s) :
      (∑ r ∈ s, ∫ ω, U i ω * U r ω ∂P) =
        ∫ ω, (U i ω) ^ 2 ∂P := by
    calc
      _ = ∫ ω, U i ω * U i ω ∂P := by
        apply Finset.sum_eq_single i
        · intro r hr hri
          exact (hoff i hi r hr (Ne.symm hri)).2
        · intro hni
          exact (hni hi).elim
      _ = ∫ ω, (U i ω) ^ 2 ∂P := by simp only [pow_two]
  have hsecond :
      (∫ ω, (∑ i ∈ s, U i ω) ^ 2 ∂P) =
        ∑ i ∈ s, ∫ ω, (U i ω) ^ 2 ∂P := by
    calc
      _ = ∫ ω, ∑ i ∈ s, ∑ r ∈ s, U i ω * U r ω ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact hsq ω
      _ = ∑ i ∈ s, ∫ ω, ∑ r ∈ s, U i ω * U r ω ∂P := by
        exact integral_finsetSum s (fun i hi => hrow i hi)
      _ = ∑ i ∈ s, ∑ r ∈ s, ∫ ω, U i ω * U r ω ∂P := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hrowIntegral i hi
      _ = ∑ i ∈ s, ∫ ω, (U i ω) ^ 2 ∂P := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hrowZero i hi
  constructor
  · convert hdouble using 1
    ext ω
    exact hsq ω
  · rw [hsecond]
    calc
      _ ≤ ∑ i ∈ s, K := Finset.sum_le_sum (fun i hi => (hdiag i hi).2)
      _ = (s.card : ℝ) * K := by simp [nsmul_eq_mul]
