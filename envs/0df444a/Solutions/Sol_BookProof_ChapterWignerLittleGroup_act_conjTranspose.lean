-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroup.act_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:59:58.848495+00:00
-- url     : https://prove2.me/submissions/2e398de1-1860-487b-a705-d1eb6cd4c8a9

-- Generated from ChapterWignerLittleGroup.lean — solution of BookProof.ChapterWignerLittleGroup.act_conjTranspose
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup



open Matrix Complex

set_option maxHeartbeats 1000000 in
theorem solution (A X : Matrix (Fin 2) (Fin 2) ℂ) (hX : Xᴴ = X) :
    (act A X)ᴴ = act A X := by

  simp [act, Matrix.conjTranspose_mul, hX, Matrix.mul_assoc]
