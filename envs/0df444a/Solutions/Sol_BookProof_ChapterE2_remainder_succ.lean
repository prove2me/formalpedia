-- Prove2me | solution 1 for BookProof.ChapterE2.remainder_succ
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:28:22.659165+00:00
-- url     : https://prove2.me/submissions/2c051f0e-4476-47a1-8cc5-36cf50f10958

-- Generated from ChapterE2.lean — solution of BookProof.ChapterE2.remainder_succ
import Mathlib
import Definitions.Def_ChapterE2
open BookProof.ChapterE2



open scoped BigOperators
open Finset

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℕ → ℝ) (N : ℕ) :
    remainder θ (N + 1) = remainder θ N * Real.sin (θ N) ^ 2 := by

  simp [remainder, Finset.prod_range_succ]
