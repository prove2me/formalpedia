-- Prove2me | solution 1 for BookProof.ChapterObservableOperator.expectation_outerProj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:47.346031+00:00
-- url     : https://prove2.me/submissions/cf2fc32a-e92d-4a85-a64e-271fa8af2fdd

-- Generated from ChapterObservableOperator.lean — solution of BookProof.ChapterObservableOperator.expectation_outerProj
import Mathlib
import Definitions.Def_ChapterObservableOperator
open BookProof.ChapterObservableOperator



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (k q : EuclideanSpace ℂ (Fin n)) :
    expectation (outerProj k) q = ((‖(inner ℂ k q : ℂ)‖ ^ 2 : ℝ) : ℂ) := by

  have hq : ∀ x y : EuclideanSpace ℂ (Fin n),
      (inner ℂ x y : ℂ) = ∑ i, (starRingEnd ℂ) (x i) * y i := by
    intro x y
    rw [PiLp.inner_apply]
    simp [RCLike.inner_apply, mul_comm]
  have hsplit : expectation (outerProj k) q
      = (∑ a, (starRingEnd ℂ) (q a) * k a) * (∑ b, (starRingEnd ℂ) (k b) * q b) := by
    rw [expectation, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [outerProj, Matrix.of_apply]
    ring
  rw [hsplit, ← hq q k, ← hq k q, ← inner_conj_symm k q,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  simp
