-- Prove2me | solution 1 for BookProof.ChapterA3.pauli_expand
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:10:19.890338+00:00
-- url     : https://prove2.me/submissions/3cf94496-67d1-4d4a-b4a6-256fd61c2148

-- Generated from ChapterA3h.lean — solution of BookProof.ChapterA3.pauli_expand
import Mathlib
import Definitions.Def_ChapterA3h
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M = ∑ μ, pauliCoeff M μ • pauliσ μ := by

  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliσ, pauliCoeff, Fin.sum_univ_four, Matrix.trace, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.diag, Matrix.add_apply] <;> ring_nf <;>
    (try simp only [Complex.I_sq]) <;> ring
