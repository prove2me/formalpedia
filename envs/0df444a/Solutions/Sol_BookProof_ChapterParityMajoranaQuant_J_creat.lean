-- Prove2me | solution 1 for BookProof.ChapterParityMajoranaQuant.J_creat
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:14:58.648932+00:00
-- url     : https://prove2.me/submissions/9a4998ff-3a24-4be4-9915-f863f2d2f4b2

-- Generated from ChapterParityMajoranaQuant.lean — solution of BookProof.ChapterParityMajoranaQuant.J_creat
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
open BookProof.ChapterParityMajoranaQuant











open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

set_option maxHeartbeats 1000000 in
theorem solution (hJ2 : J * J = -1) : J * creatProj J = Complex.I • creatProj J := by

  have key : J * (1 - iJ J) = Complex.I • (1 - iJ J) := by
    unfold iJ
    rw [mul_sub, mul_one, Matrix.mul_smul, hJ2, smul_sub, smul_smul, Complex.I_mul_I]
    module
  unfold creatProj
  rw [Matrix.mul_smul, key, smul_comm]
