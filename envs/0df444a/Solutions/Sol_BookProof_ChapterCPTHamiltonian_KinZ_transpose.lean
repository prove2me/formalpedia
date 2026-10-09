-- Prove2me | solution 1 for BookProof.ChapterCPTHamiltonian.KinZ_transpose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:52:47.496988+00:00
-- url     : https://prove2.me/submissions/755e6344-2cfa-441c-81c4-36dba7679122

-- Generated from ChapterCPTHamiltonian.lean — solution of BookProof.ChapterCPTHamiltonian.KinZ_transpose
import Mathlib
import Definitions.Def_ChapterCPTHamiltonian
open BookProof.ChapterCPTHamiltonian



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin 3) : (KinZ j)ᵀ = KinZ j := by
 revert j; decide
