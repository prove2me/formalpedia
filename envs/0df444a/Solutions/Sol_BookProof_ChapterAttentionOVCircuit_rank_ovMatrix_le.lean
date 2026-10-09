-- Prove2me | solution 1 for BookProof.ChapterAttentionOVCircuit.rank_ovMatrix_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:30:44.118597+00:00
-- url     : https://prove2.me/submissions/05bdf10a-4d01-4e20-924d-f7fb0f9da154

-- Generated from ChapterAttentionOVCircuit.lean — solution of BookProof.ChapterAttentionOVCircuit.rank_ovMatrix_le
import Mathlib
import Definitions.Def_ChapterAttentionOVCircuit
open BookProof.ChapterAttentionOVCircuit



open scoped BigOperators

noncomputable section


open Matrix BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {d n p m : ℕ}

variable {d n p m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (WO : Matrix (Fin n) (Fin d) ℝ) (WV : Matrix (Fin d) (Fin n) ℝ) :
    (ovMatrix WO WV).rank ≤ d := le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_le_width (A := WO))
