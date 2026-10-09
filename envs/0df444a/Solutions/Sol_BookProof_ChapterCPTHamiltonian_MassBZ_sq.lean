-- Prove2me | solution 1 for BookProof.ChapterCPTHamiltonian.MassBZ_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:52:07.170811+00:00
-- url     : https://prove2.me/submissions/302f62f2-f0a8-4801-8b99-d0de2f91b5cd

-- Generated from ChapterCPTHamiltonian.lean — solution of BookProof.ChapterCPTHamiltonian.MassBZ_sq
import Mathlib
import Definitions.Def_ChapterCPTHamiltonian
open BookProof.ChapterCPTHamiltonian



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : MassBZ * MassBZ = -1 := by
 decide
