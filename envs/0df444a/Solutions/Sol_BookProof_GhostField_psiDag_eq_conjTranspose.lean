-- Prove2me | solution 1 for BookProof.GhostField.psiDag_eq_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T15:45:04.612859+00:00
-- url     : https://prove2.me/submissions/4e70220e-04d6-4446-80f3-853f48e4f49f

-- Generated from ChapterGhostField.lean — solution of BookProof.GhostField.psiDag_eq_conjTranspose
import Mathlib
import Definitions.Def_ChapterGhostField
open BookProof.GhostField











open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : psiDag = psiᴴ := by

  ext i j; fin_cases i <;> fin_cases j <;> simp [psi, psiDag, Matrix.conjTranspose_apply]
