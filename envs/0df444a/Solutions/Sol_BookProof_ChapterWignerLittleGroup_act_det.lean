-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroup.act_det
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:00.345431+00:00
-- url     : https://prove2.me/submissions/b26f98d9-db3e-4d94-a3e6-59e7f0d1acae

-- Generated from ChapterWignerLittleGroup.lean — solution of BookProof.ChapterWignerLittleGroup.act_det
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup



open Matrix Complex

set_option maxHeartbeats 1000000 in
theorem solution (A X : Matrix (Fin 2) (Fin 2) ℂ) :
    (act A X).det = A.det * X.det * (starRingEnd ℂ) A.det := by

  simp [act, Matrix.det_mul, Matrix.det_conjTranspose]
