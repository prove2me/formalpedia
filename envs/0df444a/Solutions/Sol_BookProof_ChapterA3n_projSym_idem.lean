-- Prove2me | solution 1 for BookProof.ChapterA3n.projSym_idem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:50:08.734036+00:00
-- url     : https://prove2.me/submissions/699bae00-62a2-4d1c-9e16-ae4183e62b72

-- Generated from ChapterA3n.lean — solution of BookProof.ChapterA3n.projSym_idem
import Mathlib
import Definitions.Def_ChapterA3n
import Theorems.Thm_BookProof_ChapterA3n_sum_permMat_sq
open BookProof.ChapterA3n



open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j

set_option maxHeartbeats 1000000 in
theorem solution {N : ℕ} : projSym N * projSym N = projSym N := by

  have h : (Nat.factorial N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  unfold projSym
  rw [Matrix.smul_mul, Matrix.mul_smul, sum_permMat_sq, smul_smul, smul_smul,
    mul_assoc, inv_mul_cancel₀ h, mul_one]
