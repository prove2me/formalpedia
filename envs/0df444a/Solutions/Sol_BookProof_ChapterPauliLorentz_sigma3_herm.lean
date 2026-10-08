-- Prove2me | solution 1 for BookProof.ChapterPauliLorentz.sigma3_herm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T09:05:13.819979+00:00
-- url     : https://prove2.me/submissions/18207673-121c-4229-9a1b-7ee7bc6ce7a4

-- Generated from ChapterPauliLorentz.lean — solution of BookProof.ChapterPauliLorentz.sigma3_herm
import Mathlib
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliLorentz



open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution : σ3ᴴ = σ3 := by

  ext i j; fin_cases i <;> fin_cases j <;> simp [σ3, Matrix.conjTranspose_apply]
