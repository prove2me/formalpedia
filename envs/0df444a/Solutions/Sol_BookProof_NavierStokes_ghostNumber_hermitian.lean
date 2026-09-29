-- Prove2me | solution 1 for BookProof.NavierStokes.ghostNumber_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T17:07:36.827705+00:00
-- url     : https://prove2.me/submissions/5543a5dc-59fc-4e1b-995c-1f05ab25bfa9

-- Generated from ChapterNavierStokes.lean — solution of BookProof.NavierStokes.ghostNumber_hermitian
import Mathlib
import Definitions.Def_ChapterNavierStokes
import Theorems.Thm_BookProof_NavierStokes_ghostNumber_eq
open BookProof.NavierStokes













open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : ghostNumberᴴ = ghostNumber := by

  rw [ghostNumber_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
