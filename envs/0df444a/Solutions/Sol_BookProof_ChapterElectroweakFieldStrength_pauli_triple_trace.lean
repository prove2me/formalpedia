-- Prove2me | solution 1 for BookProof.ChapterElectroweakFieldStrength.pauli_triple_trace
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:33:35.479726+00:00
-- url     : https://prove2.me/submissions/86c58e4b-5193-4bf0-96d7-677214e92277

-- Generated from ChapterElectroweakFieldStrength.lean — solution of BookProof.ChapterElectroweakFieldStrength.pauli_triple_trace
import Mathlib
import Definitions.Def_ChapterElectroweakFieldStrength
open BookProof.ChapterElectroweakFieldStrength



open Matrix


open BookProof.ChapterParity BookProof.ChapterParitySU2

set_option maxHeartbeats 1000000 in
theorem solution (a b c : Fin 3) :
    (pauliV a * pauliV b * pauliV c).trace = 2 * Complex.I * eps a b c := by

  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [pauliV, pauli1, pauli2, pauli3, eps, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diag, Complex.ext_iff] <;> norm_num
