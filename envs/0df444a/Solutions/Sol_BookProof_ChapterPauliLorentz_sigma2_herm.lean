-- Prove2me | solution 1 for BookProof.ChapterPauliLorentz.sigma2_herm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T09:05:12.871981+00:00
-- url     : https://prove2.me/submissions/0eb6d0f9-c686-47ed-97fa-f29bc13440d4

-- Generated from ChapterPauliLorentz.lean — solution of BookProof.ChapterPauliLorentz.sigma2_herm
import Mathlib
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliLorentz



open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution : σ2ᴴ = σ2 := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ2, Matrix.conjTranspose_apply, Complex.conj_I]
