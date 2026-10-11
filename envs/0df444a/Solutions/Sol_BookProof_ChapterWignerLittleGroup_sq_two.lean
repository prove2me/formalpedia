-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroup.sq_two
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:10.286231+00:00
-- url     : https://prove2.me/submissions/af316811-6e45-4571-a734-6de3b79285fa

-- Generated from ChapterWignerLittleGroup.lean — solution of BookProof.ChapterWignerLittleGroup.sq_two
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup



open Matrix Complex

set_option maxHeartbeats 1000000 in
theorem solution (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by

  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring
