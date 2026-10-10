-- Prove2me | solution 1 for BookProof.ChapterObservableOperator.observableOp_expectation_real
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:50.015986+00:00
-- url     : https://prove2.me/submissions/3f628bd8-6824-48fa-8f0e-e3b672892a7a

-- Generated from ChapterObservableOperator.lean — solution of BookProof.ChapterObservableOperator.observableOp_expectation_real
import Mathlib
import Definitions.Def_ChapterObservableOperator
import Theorems.Thm_BookProof_ChapterObservableOperator_observableOp_expectation
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterObservableExpectation
open BookProof.ChapterObservableOperator



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (k : Fin m → EuclideanSpace ℂ (Fin n))
    (v : Fin m → ℝ) (q : EuclideanSpace ℂ (Fin n)) :
    (expectation (observableOp k v) q).im = 0 := by

  rw [observableOp_expectation]
  simp
