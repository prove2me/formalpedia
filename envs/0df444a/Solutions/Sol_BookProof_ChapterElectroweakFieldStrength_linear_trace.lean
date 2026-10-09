-- Prove2me | solution 1 for BookProof.ChapterElectroweakFieldStrength.linear_trace
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:33:50.600114+00:00
-- url     : https://prove2.me/submissions/5fa8f626-8d0d-4505-8b5b-076868da8d27

-- Generated from ChapterElectroweakFieldStrength.lean — solution of BookProof.ChapterElectroweakFieldStrength.linear_trace
import Mathlib
import Definitions.Def_ChapterElectroweakFieldStrength
import Theorems.Thm_BookProof_ChapterElectroweakFieldStrength_pauli_trace_orthonormal
open BookProof.ChapterElectroweakFieldStrength



open Matrix


open BookProof.ChapterParity BookProof.ChapterParitySU2

set_option maxHeartbeats 1000000 in
theorem solution (G : Fin 3 → ℂ) (j : Fin 3) :
    ((∑ m, G m • ((1 / 2 : ℂ) • pauliV m)) * pauliV j).trace = G j := by

  simp only [Fin.sum_univ_three, Matrix.smul_mul, smul_smul, Matrix.add_mul, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul, pauli_trace_orthonormal]
  fin_cases j <;> simp
