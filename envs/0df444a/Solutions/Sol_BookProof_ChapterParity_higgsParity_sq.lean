-- Prove2me | solution 1 for BookProof.ChapterParity.higgsParity_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:33.092712+00:00
-- url     : https://prove2.me/submissions/772ea40c-8033-45cb-b8af-8b079418a4ac

-- Generated from ChapterParity.lean — solution of BookProof.ChapterParity.higgsParity_sq
import Mathlib
import Definitions.Def_ChapterParity
open BookProof.ChapterParity



open Matrix
open scoped ComplexConjugate

variable {n : Type*}

set_option maxHeartbeats 1000000 in
theorem solution : higgsParity * higgsParity = -1 := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [higgsParity, pauli2, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]
