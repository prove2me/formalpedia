-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DiagonalEsa.norm_basis
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-12T15:05:54.634983+00:00
-- url     : https://prove2.me/submissions/d9513ac7-8009-4deb-9782-47c6a9ba5b46

-- Generated from ChapterNavierStokesDeficiency.lean — solution of BookProof.NavierStokesFlow.DiagonalEsa.norm_basis
import Mathlib
import Definitions.Def_ChapterNavierStokesDeficiency
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.DiagonalEsa










open scoped ENNReal











open LpNat





























open LpNat

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) : ‖basis n‖ = 1 := by

  have : ‖(basis n : L2N)‖ = ‖(1 : ℂ)‖ := lp.norm_single (by norm_num) n 1
  simpa using this
