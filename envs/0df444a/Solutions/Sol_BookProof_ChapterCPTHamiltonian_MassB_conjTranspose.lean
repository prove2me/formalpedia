-- Prove2me | solution 1 for BookProof.ChapterCPTHamiltonian.MassB_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:57:07.587812+00:00
-- url     : https://prove2.me/submissions/ed20f650-e37d-442a-8606-1543c54c6c33

-- Generated from ChapterCPTHamiltonian.lean — solution of BookProof.ChapterCPTHamiltonian.MassB_conjTranspose
import Mathlib
import Definitions.Def_ChapterCPTHamiltonian
import Theorems.Thm_BookProof_ChapterCPTHamiltonian_MassBZ_transpose
import Theorems.Thm_BookProof_ChapterCPTHamiltonian_castMat_conjTranspose
import Theorems.Thm_BookProof_ChapterCPTHamiltonian_MassB_eq_cast
open BookProof.ChapterCPTHamiltonian



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : (MassB)ᴴ = -MassB := by

  rw [MassB_eq_cast, castMat_conjTranspose, MassBZ_transpose, map_neg]
