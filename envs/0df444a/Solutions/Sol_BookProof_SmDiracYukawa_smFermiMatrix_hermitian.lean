-- Prove2me | solution 1 for BookProof.SmDiracYukawa.smFermiMatrix_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:06:52.480621+00:00
-- url     : https://prove2.me/submissions/37fec48e-beeb-49e6-bb9f-fa1e876490c1

-- Generated from ChapterSmDiracYukawa.lean — solution of BookProof.SmDiracYukawa.smFermiMatrix_hermitian
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterFarisLavine
open BookProof.SmDiracYukawa




open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {hD M : Matrix (Fin n) (Fin n) ℂ} (z : ℂ)
    (hh : hD.conjTranspose = hD) :
    (smFermiMatrix hD M z).conjTranspose = smFermiMatrix hD M z := by

  simp [smFermiMatrix, Matrix.conjTranspose_add, hh, add_comm]
