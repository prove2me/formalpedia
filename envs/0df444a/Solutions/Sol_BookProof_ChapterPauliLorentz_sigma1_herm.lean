-- Prove2me | solution 1 for BookProof.ChapterPauliLorentz.sigma1_herm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T09:05:11.710838+00:00
-- url     : https://prove2.me/submissions/9469d93a-cacb-4dae-b736-f4e7d32af99e

-- Generated from ChapterPauliLorentz.lean — solution of BookProof.ChapterPauliLorentz.sigma1_herm
import Mathlib
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliLorentz



open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution : σ1ᴴ = σ1 := by

  ext i j; fin_cases i <;> fin_cases j <;> simp [σ1, Matrix.conjTranspose_apply]
