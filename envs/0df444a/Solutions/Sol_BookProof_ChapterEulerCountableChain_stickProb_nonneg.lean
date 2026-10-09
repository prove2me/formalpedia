-- Prove2me | solution 1 for BookProof.ChapterEulerCountableChain.stickProb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:43:46.691121+00:00
-- url     : https://prove2.me/submissions/99e45ad3-010e-4085-888d-b85c775edfc5

-- Generated from ChapterEulerCountableChain.lean — solution of BookProof.ChapterEulerCountableChain.stickProb_nonneg
import Mathlib
import Definitions.Def_ChapterEulerCountableChain
import Theorems.Thm_BookProof_ChapterEulerCountableChain_stickTail_nonneg
open BookProof.ChapterEulerCountableChain



open scoped BigOperators
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 1) (n : ℕ) :
    0 ≤ stickProb c n := mul_nonneg (stickTail_nonneg c hc n) (hc n).1
