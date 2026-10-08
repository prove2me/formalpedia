-- Prove2me | solution 1 for BookProof.conjugateli_trans
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T09:05:09.580241+00:00
-- url     : https://prove2.me/submissions/3cf43741-90b3-4b7b-9168-7c9cabb0355e

-- Generated from ChapterA4.lean — solution of BookProof.conjugateli_trans
import Mathlib
import Definitions.Def_ChapterA4
open BookProof




open MeasureTheory




variable {R E E' : Type*} [Semiring R]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup E'] [Module R E] [Module R E']

variable {R E E' : Type*} [Semiring R]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup E'] [Module R E] [Module R E']

set_option maxHeartbeats 1000000 in
theorem solution (Θ : E ≃ₗᵢ[R] E') (A B : E ≃ₗᵢ[R] E) :
    conjugateₗᵢ Θ (A.trans B) = (conjugateₗᵢ Θ A).trans (conjugateₗᵢ Θ B) := by

  ext x
  simp [conjugateₗᵢ]
