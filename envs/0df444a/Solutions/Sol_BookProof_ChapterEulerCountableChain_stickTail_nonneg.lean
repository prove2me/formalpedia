-- Prove2me | solution 1 for BookProof.ChapterEulerCountableChain.stickTail_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:43:33.022542+00:00
-- url     : https://prove2.me/submissions/6b0dbb80-2c3a-4303-ba41-c0da70e6f561

-- Generated from ChapterEulerCountableChain.lean — solution of BookProof.ChapterEulerCountableChain.stickTail_nonneg
import Mathlib
import Definitions.Def_ChapterEulerCountableChain
open BookProof.ChapterEulerCountableChain



open scoped BigOperators
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 1) (N : ℕ) :
    0 ≤ stickTail c N := by

  apply Finset.prod_nonneg
  intro i _
  linarith [(hc i).2]
