-- Prove2me | solution 1 for BookProof.SmDiracYukawa.smFermiHam_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:06:55.448206+00:00
-- url     : https://prove2.me/submissions/3b3496f1-85a5-4a21-8938-7a3d55fc5896

-- Generated from ChapterSmDiracYukawa.lean — solution of BookProof.SmDiracYukawa.smFermiHam_symmetric
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiMatrix_hermitian
import Theorems.Thm_BookProof_SmCar_fermiBilin_symmetric
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmDiracYukawa




open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {hD M : Matrix (Fin n) (Fin n) ℂ} (z : ℂ)
    (hh : hD.conjTranspose = hD) (ψ φ : FermiFock n) :
    (inner ℂ (smFermiHam hD M z ψ) φ : ℂ) = inner ℂ ψ (smFermiHam hD M z φ) := fermiBilin_symmetric (smFermiMatrix_hermitian z hh) ψ φ
