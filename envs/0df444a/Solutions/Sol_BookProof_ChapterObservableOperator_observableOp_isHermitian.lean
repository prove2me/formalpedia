-- Prove2me | solution 1 for BookProof.ChapterObservableOperator.observableOp_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:44.637212+00:00
-- url     : https://prove2.me/submissions/cb289b49-8229-4a28-ae35-98cc21eab509

-- Generated from ChapterObservableOperator.lean — solution of BookProof.ChapterObservableOperator.observableOp_isHermitian
import Mathlib
import Definitions.Def_ChapterObservableOperator
import Theorems.Thm_BookProof_ChapterObservableOperator_outerProj_isHermitian
open BookProof.ChapterObservableOperator



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (k : Fin m → EuclideanSpace ℂ (Fin n)) (v : Fin m → ℝ) :
    (observableOp k v).IsHermitian := by

  unfold Matrix.IsHermitian observableOp
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_smul]
  simp [outerProj_isHermitian (k j), Matrix.IsHermitian.eq]
