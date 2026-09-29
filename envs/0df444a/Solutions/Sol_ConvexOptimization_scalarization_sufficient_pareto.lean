-- Prove2me | solution 1 for ConvexOptimization.scalarization_sufficient_pareto
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-15T03:44:01.714608+00:00
-- url     : https://prove2.me/submissions/09fc63c4-387f-4bd8-83bf-07f240b484f3

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem solution {n k : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → Fin k → ℝ)
    (lam : Fin k → ℝ) (hlam : ∀ i, 0 < lam i)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ X)
    (hmin : ∀ y ∈ X, ∑ i, lam i * f xs i ≤ ∑ i, lam i * f y i) :
    ¬∃ y ∈ X, (∀ i, f y i ≤ f xs i) ∧ f y ≠ f xs := by
  rintro ⟨y, hy, hdom, hne⟩
  have hex : ∃ i, f y i ≠ f xs i := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨i₀, hi₀⟩ := hex
  have hstrict : f y i₀ < f xs i₀ := lt_of_le_of_ne (hdom i₀) hi₀
  have hsum : ∑ i, lam i * f y i < ∑ i, lam i * f xs i := by
    apply Finset.sum_lt_sum
    · intro i hi
      exact mul_le_mul_of_nonneg_left (hdom i) (le_of_lt (hlam i))
    · exact ⟨i₀, Finset.mem_univ i₀,
        mul_lt_mul_of_pos_left hstrict (hlam i₀)⟩
  exact (not_lt_of_ge (hmin y hy)) hsum
