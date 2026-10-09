-- Prove2me | solution 1 for BookProof.ChapterEulerCountableChain.stickTail_le_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:43:33.921657+00:00
-- url     : https://prove2.me/submissions/a3ccd0b8-874e-488a-b627-9f68001a3975

-- Generated from ChapterEulerCountableChain.lean — solution of BookProof.ChapterEulerCountableChain.stickTail_le_one
import Mathlib
import Definitions.Def_ChapterEulerCountableChain
open BookProof.ChapterEulerCountableChain



open scoped BigOperators
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 1) (N : ℕ) :
    stickTail c N ≤ 1 := by

  refine Finset.prod_le_one ?_ ?_ <;> intro i _ <;> linarith [(hc i).1, (hc i).2]
