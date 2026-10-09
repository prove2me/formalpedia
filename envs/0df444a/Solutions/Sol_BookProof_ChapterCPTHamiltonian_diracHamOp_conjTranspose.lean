-- Prove2me | solution 1 for BookProof.ChapterCPTHamiltonian.diracHamOp_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:58:25.435219+00:00
-- url     : https://prove2.me/submissions/f4ef20c6-c436-42b5-8285-ffe7894eebfe

-- Generated from ChapterCPTHamiltonian.lean — solution of BookProof.ChapterCPTHamiltonian.diracHamOp_conjTranspose
import Mathlib
import Definitions.Def_ChapterCPTHamiltonian
import Theorems.Thm_BookProof_ChapterCPTHamiltonian_MassA_conjTranspose
import Theorems.Thm_BookProof_ChapterCPTHamiltonian_MassB_conjTranspose
import Theorems.Thm_BookProof_ChapterCPTHamiltonian_kinSum_conjTranspose
open BookProof.ChapterCPTHamiltonian



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (k : Fin 3 → ℝ) (m1 m2 : ℝ) :
    (diracHamOp k m1 m2)ᴴ = -diracHamOp k m1 m2 := by

  rw [diracHamOp, Matrix.conjTranspose_add, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    kinSum_conjTranspose, MassA_conjTranspose, MassB_conjTranspose]
  have hI : star Complex.I = -Complex.I := by simp
  have hm1 : star (m1 : ℂ) = (m1 : ℂ) := by simp
  have hm2 : star (m2 : ℂ) = (m2 : ℂ) := by simp
  rw [hI, hm1, hm2]
  simp only [neg_smul, smul_neg]
  abel
