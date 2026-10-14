-- Prove2me | solution 1 for BookProof.ChapterEulerCountableChain.partial_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-12T12:01:12.536413+00:00
-- url     : https://prove2.me/submissions/3b7e4019-ef5b-4530-aaed-18c92df348d2

-- Generated from ChapterEulerCountableChain.lean — solution of BookProof.ChapterEulerCountableChain.partial_sum
import Mathlib
import Definitions.Def_ChapterEulerCountableChain
import Theorems.Thm_BookProof_ChapterEulerCountableChain_stickTail_succ
open BookProof.ChapterEulerCountableChain



open scoped BigOperators
open Filter Topology

set_option maxHeartbeats 1000000 in

theorem solution (c : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, stickProb c n = 1 - stickTail c N := by
  induction N with
  | zero => simp [stickTail]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, stickTail_succ]
      unfold stickProb
      ring
