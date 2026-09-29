-- Prove2me | solution 1 for BookProof.NavierStokes.ghostCreate_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:43:06.586634+00:00
-- url     : https://prove2.me/submissions/ccb327bd-971c-41ee-8f8e-6a5f338fc5e7

-- Generated from ChapterNavierStokes.lean — solution of BookProof.NavierStokes.ghostCreate_sq
import Mathlib
import Definitions.Def_ChapterNavierStokes
import Theorems.Thm_BookProof_NavierStokes_ghostCreate_eq
open BookProof.NavierStokes













open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : ghostCreate * ghostCreate = 0 := by

  rw [ghostCreate_eq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
