-- Prove2me | solution 1 for BookProof.ChapterObservableOperator.observableOp_expectation
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:48.650312+00:00
-- url     : https://prove2.me/submissions/7cd89517-d972-485c-b428-6f0c903a0759

-- Generated from ChapterObservableOperator.lean — solution of BookProof.ChapterObservableOperator.observableOp_expectation
import Mathlib
import Definitions.Def_ChapterObservableOperator
import Theorems.Thm_BookProof_ChapterObservableOperator_expectation_outerProj
import Theorems.Thm_BookProof_ChapterObservableExpectation_observableExpectation_scalar
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterObservableExpectation
open BookProof.ChapterObservableOperator



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (k : Fin m → EuclideanSpace ℂ (Fin n)) (v : Fin m → ℝ)
    (q : EuclideanSpace ℂ (Fin n)) :
    expectation (observableOp k v) q
      = ((BookProof.ChapterObservableExpectation.observableExpectation
            (bornProb k q) v : ℝ) : ℂ) := by

  have key : ∀ a b : Fin n, (starRingEnd ℂ) (q a) * (observableOp k v) a b * q b
      = ∑ j, (v j : ℂ) * ((starRingEnd ℂ) (q a) * outerProj (k j) a b * q b) := by
    intro a b
    simp only [observableOp, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hlin : expectation (observableOp k v) q
      = ∑ j, (v j : ℂ) * expectation (outerProj (k j)) q :=
    calc expectation (observableOp k v) q
        = ∑ a, ∑ b, ∑ j, (v j : ℂ) * ((starRingEnd ℂ) (q a) * outerProj (k j) a b * q b) := by
          simp only [expectation, key]
      _ = ∑ a, ∑ j, ∑ b, (v j : ℂ) * ((starRingEnd ℂ) (q a) * outerProj (k j) a b * q b) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ j, ∑ a, ∑ b, (v j : ℂ) * ((starRingEnd ℂ) (q a) * outerProj (k j) a b * q b) :=
          Finset.sum_comm
      _ = ∑ j, (v j : ℂ) * expectation (outerProj (k j)) q := by
          simp only [expectation, Finset.mul_sum]
  rw [hlin, BookProof.ChapterObservableExpectation.observableExpectation_scalar]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [expectation_outerProj]
  simp [bornProb, mul_comm]
