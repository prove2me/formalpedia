-- Prove2me | solution 1 for BookProof.NavierStokes.ghostCreate_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T15:57:18.555666+00:00
-- url     : https://prove2.me/submissions/deb6331b-bb6d-4c43-89c5-7fb126de2298

-- Generated from ChapterNavierStokes.lean — solution of BookProof.NavierStokes.ghostCreate_eq
import Mathlib
import Definitions.Def_ChapterNavierStokes
open BookProof.NavierStokes













open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : ghostCreate = !![0, 1; 0, 0] := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ghostCreate, ghostAnnih, Matrix.conjTranspose_apply]
