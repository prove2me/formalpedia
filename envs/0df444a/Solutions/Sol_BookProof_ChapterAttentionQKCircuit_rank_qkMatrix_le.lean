-- Prove2me | solution 1 for BookProof.ChapterAttentionQKCircuit.rank_qkMatrix_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:36:42.409048+00:00
-- url     : https://prove2.me/submissions/635bd98d-467f-4309-a777-5317e97ee7c8

-- Generated from ChapterAttentionQKCircuit.lean — solution of BookProof.ChapterAttentionQKCircuit.rank_qkMatrix_le
import Mathlib
import Definitions.Def_ChapterAttentionQKCircuit
open BookProof.ChapterAttentionQKCircuit



open scoped BigOperators

noncomputable section


open Matrix BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {d n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {d n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (WQ WK : Matrix (Fin d) (Fin n) ℝ) : (qkMatrix WQ WK).rank ≤ d := le_trans (Matrix.rank_mul_le_left _ _) (by simpa using Matrix.rank_le_width (A := WQᵀ))
