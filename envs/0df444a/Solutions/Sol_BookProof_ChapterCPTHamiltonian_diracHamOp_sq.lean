-- Prove2me | solution 1 for BookProof.ChapterCPTHamiltonian.diracHamOp_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:58:38.420207+00:00
-- url     : https://prove2.me/submissions/73e3bd74-d6b3-4436-b9e5-b7e4985664c6

-- Generated from ChapterCPTHamiltonian.lean — solution of BookProof.ChapterCPTHamiltonian.diracHamOp_sq
import Mathlib
import Definitions.Def_ChapterCPTHamiltonian
open BookProof.ChapterCPTHamiltonian



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (k : Fin 3 → ℝ) (m1 m2 : ℝ) :
    diracHamOp k m1 m2 * diracHamOp k m1 m2
      = (-((∑ j : Fin 3, (k j : ℂ) ^ 2) + (m1 : ℂ) ^ 2 + (m2 : ℂ) ^ 2))
          • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by

  unfold diracHamOp Kin MassA MassB
  simp [Fin.sum_univ_three, dgamma, dgamma5]
  simp [mgamma, mgamma5]
  simp [mgammaZ, mgamma5Z]
  simp [← Matrix.ext_iff, Fin.forall_fin_succ, Matrix.mul_apply,
    Fin.sum_univ_succ] at *
  ring_nf
  norm_num [Complex.ext_iff, sq]
  ring
