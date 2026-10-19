-- Prove2me | solution 1 for BookProof.SmDiracSpinor.diracFieldHam_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:06:48.619209+00:00
-- url     : https://prove2.me/submissions/3d5c6feb-a59f-4bb3-86b8-48964211deb7

-- Generated from ChapterSmDiracSpinor.lean — solution of BookProof.SmDiracSpinor.diracFieldHam_symmetric
import Mathlib
import Definitions.Def_ChapterSmDiracSpinor
import Theorems.Thm_BookProof_SmDiracSpinor_diracOneParticle_hermitian
import Theorems.Thm_BookProof_SmCar_fermiBilin_symmetric
import Definitions.Def_ChapterCPTHamiltonian
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmDiracSpinor




open Matrix
open BookProof.ChapterCPTHamiltonian BookProof.SmCar BookProof.SmDiracYukawa
open BookProof.FarisLavine

noncomputable section

variable {k : Fin 3 → ℝ} {m1 m2 : ℝ}

variable {k : Fin 3 → ℝ} {m1 m2 : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (psi phi : FermiFock 4) :
    (inner ℂ (diracFieldHam k m1 m2 psi) phi : ℂ)
      = inner ℂ psi (diracFieldHam k m1 m2 phi) := fermiBilin_symmetric diracOneParticle_hermitian psi phi
