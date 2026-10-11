-- Prove2me | solution 1 for BookProof.ChapterParity.dgamma0_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:10:52.295+00:00
-- url     : https://prove2.me/submissions/25fa5ebe-71f8-4102-ace0-bf6f59082f2f

-- Generated from ChapterParity.lean — solution of BookProof.ChapterParity.dgamma0_sq
import Mathlib
import Definitions.Def_ChapterParity
import Theorems.Thm_BookProof_ChapterParity_mgamma0_sq
import Definitions.Def_ChapterA3
open BookProof.ChapterParity



open Matrix
open scoped ComplexConjugate
open BookProof.ChapterA3

variable {n : Type*}

set_option maxHeartbeats 1000000 in

theorem solution : dgamma 0 * dgamma 0 = 1 := by
  simp only [dgamma, Matrix.smul_mul, Matrix.mul_smul, smul_smul, neg_mul_neg, Complex.I_mul_I]
  rw [mgamma0_sq]
  simp

/-! ## 4. The Gell-Mann matrices and the outer-automorphism (parity) signs -/
