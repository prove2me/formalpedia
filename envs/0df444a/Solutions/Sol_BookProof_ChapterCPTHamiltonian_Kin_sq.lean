-- Prove2me | solution 1 for BookProof.ChapterCPTHamiltonian.Kin_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:55:09.488282+00:00
-- url     : https://prove2.me/submissions/db989df9-436e-4bfe-8716-6c74f7f6e12e

-- Generated from ChapterCPTHamiltonian.lean — solution of BookProof.ChapterCPTHamiltonian.Kin_sq
import Mathlib
import Definitions.Def_ChapterCPTHamiltonian
import Theorems.Thm_BookProof_ChapterCPTHamiltonian_KinZ_sq
import Theorems.Thm_BookProof_ChapterCPTHamiltonian_Kin_eq_cast
open BookProof.ChapterCPTHamiltonian



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin 3) : Kin j * Kin j = 1 := by

  rw [Kin_eq_cast, ← map_mul, KinZ_sq, map_one]
