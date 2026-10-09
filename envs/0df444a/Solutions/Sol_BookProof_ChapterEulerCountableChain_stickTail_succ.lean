-- Prove2me | solution 1 for BookProof.ChapterEulerCountableChain.stickTail_succ
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:43:07.880344+00:00
-- url     : https://prove2.me/submissions/f14a826a-fa2a-4ad0-baa7-b17ccc8888e3

-- Generated from ChapterEulerCountableChain.lean — solution of BookProof.ChapterEulerCountableChain.stickTail_succ
import Mathlib
import Definitions.Def_ChapterEulerCountableChain
open BookProof.ChapterEulerCountableChain



open scoped BigOperators
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution (c : ℕ → ℝ) (N : ℕ) :
    stickTail c (N + 1) = stickTail c N * (1 - c N) := by

  simp [stickTail, Finset.prod_range_succ]
