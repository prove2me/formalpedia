-- Prove2me | solution 1 for BookProof.ChapterParity.pauli2_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:31.721585+00:00
-- url     : https://prove2.me/submissions/14d00a5a-9e13-4da9-a5a4-a0939954a5a3

-- Generated from ChapterParity.lean — solution of BookProof.ChapterParity.pauli2_sq
import Mathlib
import Definitions.Def_ChapterParity
open BookProof.ChapterParity



open Matrix
open scoped ComplexConjugate

variable {n : Type*}

set_option maxHeartbeats 1000000 in
theorem solution : pauli2 * pauli2 = 1 := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauli2, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]
