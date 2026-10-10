-- Prove2me | solution 1 for BookProof.ChapterParitySU2.pauliV_pseudoreal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:13:09.993993+00:00
-- url     : https://prove2.me/submissions/51a42094-c056-4f26-8c9d-eeaabc141c37

-- Generated from ChapterParitySU2.lean — solution of BookProof.ChapterParitySU2.pauliV_pseudoreal
import Mathlib
import Definitions.Def_ChapterParitySU2
import Definitions.Def_ChapterParity
open BookProof.ChapterParitySU2



open Matrix
open scoped ComplexConjugate


open BookProof.ChapterParity

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin 3) :
    pauli2 * pauliV j * pauli2 = -((pauliV j).map (starRingEnd ℂ)) := by

  fin_cases j <;>
  · ext a b; fin_cases a <;> fin_cases b <;>
      simp [pauliV, pauli1, pauli3, pauli2, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.map_apply, Complex.conj_I]
