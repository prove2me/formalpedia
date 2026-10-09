-- Prove2me | solution 1 for BookProof.ChapterCPTHamiltonian.kinSum_MassB_anticomm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:57:48.247109+00:00
-- url     : https://prove2.me/submissions/208356ed-2d30-426e-a2f6-dea82847444b

-- Generated from ChapterCPTHamiltonian.lean — solution of BookProof.ChapterCPTHamiltonian.kinSum_MassB_anticomm
import Mathlib
import Definitions.Def_ChapterCPTHamiltonian
import Theorems.Thm_BookProof_ChapterCPTHamiltonian_Kin_MassB_anticomm
open BookProof.ChapterCPTHamiltonian



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (k : Fin 3 → ℝ) :
    (∑ j : Fin 3, (k j : ℂ) • Kin j) * MassB + MassB * (∑ j : Fin 3, (k j : ℂ) • Kin j)
      = 0 := by

  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun i _ => by
    rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add, Kin_MassB_anticomm i, smul_zero]
