-- Prove2me | solution 1 for BookProof.ChapterCPTHamiltonian.Kin_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:56:29.642303+00:00
-- url     : https://prove2.me/submissions/13ddf26e-ea53-454c-8941-91c6d6fad711

-- Generated from ChapterCPTHamiltonian.lean — solution of BookProof.ChapterCPTHamiltonian.Kin_conjTranspose
import Mathlib
import Definitions.Def_ChapterCPTHamiltonian
import Theorems.Thm_BookProof_ChapterCPTHamiltonian_KinZ_transpose
import Theorems.Thm_BookProof_ChapterCPTHamiltonian_castMat_conjTranspose
import Theorems.Thm_BookProof_ChapterCPTHamiltonian_Kin_eq_cast
open BookProof.ChapterCPTHamiltonian



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin 3) : (Kin j)ᴴ = Kin j := by

  rw [Kin_eq_cast, castMat_conjTranspose, KinZ_transpose]
