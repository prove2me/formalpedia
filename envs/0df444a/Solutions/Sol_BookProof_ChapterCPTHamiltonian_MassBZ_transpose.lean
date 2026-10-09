-- Prove2me | solution 1 for BookProof.ChapterCPTHamiltonian.MassBZ_transpose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:53:16.150687+00:00
-- url     : https://prove2.me/submissions/c0c00ebb-a8ae-4f57-8e18-dbee5fb8b28b

-- Generated from ChapterCPTHamiltonian.lean — solution of BookProof.ChapterCPTHamiltonian.MassBZ_transpose
import Mathlib
import Definitions.Def_ChapterCPTHamiltonian
open BookProof.ChapterCPTHamiltonian



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : (MassBZ)ᵀ = -MassBZ := by
 decide
