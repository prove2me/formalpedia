-- Prove2me | solution 1 for BookProof.ChapterObservableExpectation.observableExpectation_add_left
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:37.239405+00:00
-- url     : https://prove2.me/submissions/aeac1f39-59f5-447f-85dd-e9975fc541e2

-- Generated from ChapterObservableExpectation.lean — solution of BookProof.ChapterObservableExpectation.observableExpectation_add_left
import Mathlib
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterObservableExpectation



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn

variable {m n : ℕ}
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

variable {m n : ℕ}
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (p q : Fin m → ℝ) (v : Fin m → E) :
    observableExpectation (fun j => p j + q j) v
      = observableExpectation p v + observableExpectation q v := by

  simp [observableExpectation, add_smul, Finset.sum_add_distrib]
