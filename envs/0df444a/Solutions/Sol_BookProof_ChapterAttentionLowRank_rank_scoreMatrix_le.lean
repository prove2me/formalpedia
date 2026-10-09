-- Prove2me | solution 1 for BookProof.ChapterAttentionLowRank.rank_scoreMatrix_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:43:27.771085+00:00
-- url     : https://prove2.me/submissions/5fe00468-9ac7-4209-b5ca-ae55fe313b5a

-- Generated from ChapterAttentionLowRank.lean — solution of BookProof.ChapterAttentionLowRank.rank_scoreMatrix_le
import Mathlib
import Definitions.Def_ChapterAttentionLowRank
import Theorems.Thm_BookProof_ChapterAttentionLowRank_scoreMatrix_eq_mul
open BookProof.ChapterAttentionLowRank



open scoped BigOperators

noncomputable section


variable {m d : ℕ}

variable {m d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (Q K : Fin m → Fin d → ℝ) :
    (scoreMatrix Q K).rank ≤ d := by

  rw [scoreMatrix_eq_mul]
  refine le_trans (Matrix.rank_mul_le_left _ _) ?_
  simpa using (Matrix.rank_le_width (A := (Matrix.of Q)))
