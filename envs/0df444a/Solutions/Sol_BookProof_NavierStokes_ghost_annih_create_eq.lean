-- Prove2me | solution 1 for BookProof.NavierStokes.ghost_annih_create_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:47:59.684632+00:00
-- url     : https://prove2.me/submissions/8d0b8915-a6a4-4e02-8bb3-5a7c6c122133

-- Generated from ChapterNavierStokes.lean — solution of BookProof.NavierStokes.ghost_annih_create_eq
import Mathlib
import Definitions.Def_ChapterNavierStokes
import Theorems.Thm_BookProof_NavierStokes_ghostCreate_eq
open BookProof.NavierStokes













open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : ghostAnnih * ghostCreate = !![0, 0; 0, 1] := by

  rw [ghostCreate_eq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ghostAnnih, Matrix.mul_apply, Fin.sum_univ_two]
