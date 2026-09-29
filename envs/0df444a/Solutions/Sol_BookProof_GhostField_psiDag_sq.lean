-- Prove2me | solution 1 for BookProof.GhostField.psiDag_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T15:46:31.373838+00:00
-- url     : https://prove2.me/submissions/8fd04f8e-7de6-440e-80f0-8b23dc6f8669

-- Generated from ChapterGhostField.lean — solution of BookProof.GhostField.psiDag_sq
import Mathlib
import Definitions.Def_ChapterGhostField
open BookProof.GhostField











open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : psiDag * psiDag = 0 := by

  ext i j; fin_cases i <;> fin_cases j <;> simp [psiDag, Matrix.mul_apply, Fin.sum_univ_two]
