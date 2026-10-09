-- Prove2me | solution 1 for BookProof.ChapterEulerCountableChain.stickProb_euler
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:44:51.641357+00:00
-- url     : https://prove2.me/submissions/14bc796f-e993-4ddf-ac26-bf2c997f4dba

-- Generated from ChapterEulerCountableChain.lean — solution of BookProof.ChapterEulerCountableChain.stickProb_euler
import Mathlib
import Definitions.Def_ChapterEulerCountableChain
import Theorems.Thm_BookProof_ChapterEulerCountableChain_one_sub_condCos
open BookProof.ChapterEulerCountableChain



open scoped BigOperators
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℕ → ℝ) (n : ℕ) :
    stickProb (condCos θ) n
      = (∏ k ∈ Finset.range n, Real.sin (θ k) ^ 2) * Real.cos (θ n) ^ 2 := by

  unfold stickProb stickTail condCos
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  have h := one_sub_condCos θ k
  rw [condCos] at h
  linarith
