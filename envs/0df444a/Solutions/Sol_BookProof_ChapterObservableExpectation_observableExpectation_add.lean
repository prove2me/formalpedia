-- Prove2me | solution 1 for BookProof.ChapterObservableExpectation.observableExpectation_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:34.672983+00:00
-- url     : https://prove2.me/submissions/c9f2123a-168b-4319-81f0-e1adcbfe9eea

-- Generated from ChapterObservableExpectation.lean — solution of BookProof.ChapterObservableExpectation.observableExpectation_add
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
theorem solution (p : Fin m → ℝ) (v w : Fin m → E) :
    observableExpectation p (fun j => v j + w j)
      = observableExpectation p v + observableExpectation p w := by

  simp [observableExpectation, smul_add, Finset.sum_add_distrib]
