-- Prove2me | solution 1 for BookProof.ChapterObservableExpectation.observableExpectation_const
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:33.117776+00:00
-- url     : https://prove2.me/submissions/082f5f17-33db-4d4a-8120-addae1a9a946

-- Generated from ChapterObservableExpectation.lean — solution of BookProof.ChapterObservableExpectation.observableExpectation_const
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
theorem solution (p : Fin m → ℝ) (hp : ∑ j, p j = 1) (c : E) :
    observableExpectation p (fun _ => c) = c := by

  rw [observableExpectation, ← Finset.sum_smul, hp, one_smul]
