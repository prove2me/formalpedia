-- Prove2me | solution 1 for BookProof.ChapterElectroweakFieldStrength.pauli_trace_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:33:34.568263+00:00
-- url     : https://prove2.me/submissions/6ef34366-9471-4364-b240-af9801d938e9

-- Generated from ChapterElectroweakFieldStrength.lean — solution of BookProof.ChapterElectroweakFieldStrength.pauli_trace_orthonormal
import Mathlib
import Definitions.Def_ChapterElectroweakFieldStrength
open BookProof.ChapterElectroweakFieldStrength



open Matrix


open BookProof.ChapterParity BookProof.ChapterParitySU2

set_option maxHeartbeats 1000000 in
theorem solution (a b : Fin 3) :
    (pauliV a * pauliV b).trace = 2 * (if a = b then 1 else 0) := by

  fin_cases a <;> fin_cases b <;>
    simp [pauliV, pauli1, pauli2, pauli3, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diag] <;> norm_num
