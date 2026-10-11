-- Prove2me | solution 1 for BookProof.SmDiracSpinor.diracOneParticle_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:35:14.110153+00:00
-- url     : https://prove2.me/submissions/7b234ec9-c766-4e24-b941-2893114afc4c

-- Generated from ChapterSmDiracSpinor.lean — solution of BookProof.SmDiracSpinor.diracOneParticle_hermitian
import Mathlib
import Definitions.Def_ChapterSmDiracSpinor
import Theorems.Thm_BookProof_ChapterCPTHamiltonian_diracHamOp_conjTranspose
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterCPTHamiltonian
open BookProof.SmDiracSpinor




open Matrix
open BookProof.ChapterCPTHamiltonian BookProof.SmCar BookProof.SmDiracYukawa
open BookProof.FarisLavine

noncomputable section

variable {k : Fin 3 → ℝ} {m1 m2 : ℝ}

variable {k : Fin 3 → ℝ} {m1 m2 : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution :
    (diracOneParticle k m1 m2).conjTranspose = diracOneParticle k m1 m2 := by

  rw [diracOneParticle, Matrix.conjTranspose_smul, diracHamOp_conjTranspose]
  have hI : star (-Complex.I) = Complex.I := by simp
  rw [hI]
  simp [smul_neg, neg_smul]
