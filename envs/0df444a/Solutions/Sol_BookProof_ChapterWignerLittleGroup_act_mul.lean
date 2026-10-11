-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroup.act_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:12.095834+00:00
-- url     : https://prove2.me/submissions/27393488-af2b-4df7-84c0-fafb875a22ce

-- Generated from ChapterWignerLittleGroup.lean — solution of BookProof.ChapterWignerLittleGroup.act_mul
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup



open Matrix Complex

set_option maxHeartbeats 1000000 in
theorem solution (A B X : Matrix (Fin 2) (Fin 2) ℂ) :
    act (A * B) X = act A (act B X) := by

  simp [act, Matrix.conjTranspose_mul, Matrix.mul_assoc]
