-- Prove2me | solution 1 for BookProof.conjugateli_symm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T09:05:08.571678+00:00
-- url     : https://prove2.me/submissions/9003be3f-9d9b-4803-92a9-552a16669dc5

-- Generated from ChapterA4.lean — solution of BookProof.conjugateli_symm
import Mathlib
import Definitions.Def_ChapterA4
open BookProof




open MeasureTheory




variable {R E E' : Type*} [Semiring R]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup E'] [Module R E] [Module R E']

variable {R E E' : Type*} [Semiring R]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup E'] [Module R E] [Module R E']

set_option maxHeartbeats 1000000 in
theorem solution (Θ : E ≃ₗᵢ[R] E') (A : E ≃ₗᵢ[R] E) :
    (conjugateₗᵢ Θ A).symm = conjugateₗᵢ Θ A.symm := by

  ext x
  simp [conjugateₗᵢ]
