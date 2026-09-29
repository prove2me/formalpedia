-- Prove2me | solution 1 for BookProof.NavierStokes.ghostAnnih_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T15:55:36.112725+00:00
-- url     : https://prove2.me/submissions/210f1c47-aa36-4c14-8b18-409fe7d6ce89

-- Generated from ChapterNavierStokes.lean — solution of BookProof.NavierStokes.ghostAnnih_sq
import Mathlib
import Definitions.Def_ChapterNavierStokes
open BookProof.NavierStokes













open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : ghostAnnih * ghostAnnih = 0 := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ghostAnnih, Matrix.mul_apply, Fin.sum_univ_two]
