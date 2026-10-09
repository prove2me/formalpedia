-- Prove2me | solution 1 for BookProof.ChapterCPTHamiltonian.MassAZ_transpose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:53:15.276984+00:00
-- url     : https://prove2.me/submissions/ceaf43c4-67a6-4064-b5a7-14f037bf7471

-- Generated from ChapterCPTHamiltonian.lean — solution of BookProof.ChapterCPTHamiltonian.MassAZ_transpose
import Mathlib
import Definitions.Def_ChapterCPTHamiltonian
open BookProof.ChapterCPTHamiltonian



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : (MassAZ)ᵀ = -MassAZ := by
 decide
