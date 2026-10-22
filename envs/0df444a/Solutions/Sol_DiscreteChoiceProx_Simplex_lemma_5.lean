-- Prove2me | solution 1 for DiscreteChoiceProx.Simplex.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-21T06:38:20.40041+00:00
-- url     : https://prove2.me/submissions/5947a17d-95f8-49e4-bbd9-f3a75127d66b

import Definitions.Def_DiscreteChoiceProx_Simplex_Model
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Independently written formal proof of Müller--Nesterov--Shikhman,
arXiv:1909.05591v1, Lemma 5, PDF p.11.
The absolute sum of each row is twice its diagonal entry; the triangle
inequality then bounds every image of the coordinate unit cube.
-/

open Finset DiscreteChoiceProx.Simplex

namespace Oct21FiveMatrixNorm

theorem row_abs_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ClassA A) (i : Fin n) :
    ∑ j, |A i j| = 2 * A i i := by
  classical
  have heach (j : Fin n) : |A i j| = if j = i then A i i else -A i j := by
    by_cases hji : j = i
    · subst j
      simp [hA.2.1 i]
    · simp only [if_neg hji]
      exact abs_of_nonpos (hA.2.2.1 i j (Ne.symm hji))
  calc
    ∑ j, |A i j| = ∑ j, (if j = i then A i i else -A i j) := by
      apply sum_congr rfl
      intro j _
      exact heach j
    _ = A i i + ∑ j ∈ univ.erase i, -A i j := by
      rw [← sum_erase_add _ _ (mem_univ i)]
      simp only [if_pos rfl]
      rw [add_comm]
      congr 1
      apply sum_congr rfl
      intro j hj
      simp only [mem_erase] at hj
      simp [hj.1]
    _ = 2 * A i i := by
      have hrow := hA.2.2.2 i
      rw [← sum_erase_add _ _ (mem_univ i)] at hrow
      rw [sum_neg_distrib]
      linarith

theorem unit_cube_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ClassA A) (z : Fin n → ℝ) (hz : ∀ j, |z j| ≤ 1) :
    norm1 (A.mulVec z) ≤ 2 * A.trace := by
  calc
    norm1 (A.mulVec z) = ∑ i, |∑ j, A i j * z j| := rfl
    _ ≤ ∑ i, ∑ j, |A i j * z j| := by
      apply sum_le_sum
      intro i _
      exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |A i j| := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_left (hz j) (abs_nonneg (A i j))
    _ = ∑ i, 2 * A i i := by
      apply sum_congr rfl
      intro i _
      exact row_abs_sum A hA i
    _ = 2 * A.trace := by
      rw [← mul_sum]
      rfl

end Oct21FiveMatrixNorm

theorem solution {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ClassA A) : normInfOne A ≤ 2 * A.trace := by
  apply csSup_le
  · refine ⟨norm1 (A.mulVec 0), ?_⟩
    exact ⟨0, by simp, rfl⟩
  · rintro y ⟨z, hz, rfl⟩
    exact Oct21FiveMatrixNorm.unit_cube_bound A hA z hz

#print axioms solution
