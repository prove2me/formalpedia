-- Prove2me | solution 1 for BookProof.ChapterCPTHamiltonian.KinZ_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:51:27.294074+00:00
-- url     : https://prove2.me/submissions/13a3d416-aede-42e7-9083-7adedb52b0c0

-- Generated from ChapterCPTHamiltonian.lean — solution of BookProof.ChapterCPTHamiltonian.KinZ_sq
import Mathlib
import Definitions.Def_ChapterCPTHamiltonian
open BookProof.ChapterCPTHamiltonian



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin 3) : KinZ j * KinZ j = 1 := by
 revert j; decide
