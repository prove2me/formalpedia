-- Prove2me | solution 1 for BookProof.ChapterObservableExpectation.observableExpectation_scalar
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:31.790191+00:00
-- url     : https://prove2.me/submissions/65be5bdc-2ea2-443e-bcc5-09d05f481433

-- Generated from ChapterObservableExpectation.lean — solution of BookProof.ChapterObservableExpectation.observableExpectation_scalar
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
theorem solution (p v : Fin m → ℝ) :
    observableExpectation p v = ∑ j, p j * v j := by

  simp [observableExpectation, smul_eq_mul]
