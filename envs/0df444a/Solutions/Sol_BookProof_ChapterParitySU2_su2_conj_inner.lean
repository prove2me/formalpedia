-- Prove2me | solution 1 for BookProof.ChapterParitySU2.su2_conj_inner
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:13:11.316866+00:00
-- url     : https://prove2.me/submissions/0c492e5c-cfa0-4cb8-9889-8c6cbeb83a48

-- Generated from ChapterParitySU2.lean — solution of BookProof.ChapterParitySU2.su2_conj_inner
import Mathlib
import Definitions.Def_ChapterParitySU2
import Definitions.Def_ChapterParity
open BookProof.ChapterParitySU2



open Matrix
open scoped ComplexConjugate


open BookProof.ChapterParity

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin 3) :
    (su2gen j).map (starRingEnd ℂ) = pauli2 * su2gen j * pauli2 := by

  fin_cases j <;>
  · ext a b; fin_cases a <;> fin_cases b <;>
      simp [su2gen, pauliV, pauli1, pauli3, pauli2, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.map_apply, Complex.conj_I, Complex.I_mul_I]
