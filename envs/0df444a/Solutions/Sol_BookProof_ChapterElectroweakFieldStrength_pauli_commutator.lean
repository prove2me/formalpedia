-- Prove2me | solution 1 for BookProof.ChapterElectroweakFieldStrength.pauli_commutator
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:33:48.584983+00:00
-- url     : https://prove2.me/submissions/d0521076-b4ce-4d1a-a5de-3e51a96bd9d0

-- Generated from ChapterElectroweakFieldStrength.lean — solution of BookProof.ChapterElectroweakFieldStrength.pauli_commutator
import Mathlib
import Definitions.Def_ChapterElectroweakFieldStrength
open BookProof.ChapterElectroweakFieldStrength



open Matrix


open BookProof.ChapterParity BookProof.ChapterParitySU2

set_option maxHeartbeats 1000000 in
theorem solution (k l : Fin 3) :
    pauliV k * pauliV l - pauliV l * pauliV k = (2 * Complex.I) • ∑ m, eps k l m • pauliV m := by

  fin_cases k <;> fin_cases l <;>
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [pauliV, pauli1, pauli2, pauli3, eps,
          Matrix.smul_apply, Complex.ext_iff] <;> norm_num
