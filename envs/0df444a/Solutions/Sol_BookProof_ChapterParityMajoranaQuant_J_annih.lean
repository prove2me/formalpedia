-- Prove2me | solution 1 for BookProof.ChapterParityMajoranaQuant.J_annih
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:14:56.306717+00:00
-- url     : https://prove2.me/submissions/b86b1ac0-1e91-4e7f-b0df-b8018bc7147e

-- Generated from ChapterParityMajoranaQuant.lean — solution of BookProof.ChapterParityMajoranaQuant.J_annih
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
open BookProof.ChapterParityMajoranaQuant











open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

set_option maxHeartbeats 1000000 in
theorem solution (hJ2 : J * J = -1) : J * annihProj J = (-Complex.I) • annihProj J := by

  have key : J * (1 + iJ J) = (-Complex.I) • (1 + iJ J) := by
    unfold iJ
    rw [mul_add, mul_one, Matrix.mul_smul, hJ2, smul_add, smul_smul, neg_mul, Complex.I_mul_I]
    module
  unfold annihProj
  rw [Matrix.mul_smul, key, smul_comm]
