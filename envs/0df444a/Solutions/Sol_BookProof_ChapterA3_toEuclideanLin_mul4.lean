-- Prove2me | solution 1 for BookProof.ChapterA3.toEuclideanLin_mul4
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:01.610461+00:00
-- url     : https://prove2.me/submissions/203c51cc-4707-4898-86e8-17f580a8d5eb

-- Generated from ChapterPauliCommutant.lean — solution of BookProof.ChapterA3.toEuclideanLin_mul4
import Mathlib
import Definitions.Def_ChapterPauliCommutant
import Definitions.Def_ChapterA3
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix.toEuclideanLin (A * B)
      = (Matrix.toEuclideanLin A) ∘ₗ (Matrix.toEuclideanLin B) := by

  ext x i
  simp [Matrix.mulVec_mulVec]
