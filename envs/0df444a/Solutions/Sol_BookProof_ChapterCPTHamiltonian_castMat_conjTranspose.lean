-- Prove2me | solution 1 for BookProof.ChapterCPTHamiltonian.castMat_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:53:28.903502+00:00
-- url     : https://prove2.me/submissions/c8c01b8a-8bec-486d-b192-d1c209ad9ab4

-- Generated from ChapterCPTHamiltonian.lean — solution of BookProof.ChapterCPTHamiltonian.castMat_conjTranspose
import Mathlib
import Definitions.Def_ChapterCPTHamiltonian
open BookProof.ChapterCPTHamiltonian



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (M : Matrix (Fin 4) (Fin 4) ℤ) :
    ((Int.castRingHom ℂ).mapMatrix M)ᴴ = (Int.castRingHom ℂ).mapMatrix Mᵀ := by

  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.conjTranspose_apply,
    Matrix.transpose_apply]
