-- Prove2me | solution 1 for BookProof.ChapterPauliLorentz.hermMat_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:04:28.565218+00:00
-- url     : https://prove2.me/submissions/ad777611-b2a3-47b8-94da-1867efa0e4d2

-- Generated from ChapterPauliLorentz.lean — solution of BookProof.ChapterPauliLorentz.hermMat_isHermitian
import Mathlib
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliLorentz



open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (x : Fin 4 → ℝ) : (hermMat x)ᴴ = hermMat x := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hermMat, Matrix.conjTranspose_apply, Complex.conj_I] ; ring
