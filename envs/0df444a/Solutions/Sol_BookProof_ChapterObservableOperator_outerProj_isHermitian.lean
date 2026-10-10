-- Prove2me | solution 1 for BookProof.ChapterObservableOperator.outerProj_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:43.266331+00:00
-- url     : https://prove2.me/submissions/9de29d69-126d-4922-9074-825fd14b0aa9

-- Generated from ChapterObservableOperator.lean — solution of BookProof.ChapterObservableOperator.outerProj_isHermitian
import Mathlib
import Definitions.Def_ChapterObservableOperator
open BookProof.ChapterObservableOperator



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (k : EuclideanSpace ℂ (Fin n)) :
    (outerProj k).IsHermitian := by

  ext a b
  simp [outerProj, Matrix.conjTranspose_apply, mul_comm]
