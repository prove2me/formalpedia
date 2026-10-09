-- Prove2me | solution 1 for BookProof.ChapterAttentionStreaming.snoc_denom_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:42:49.455969+00:00
-- url     : https://prove2.me/submissions/fe536817-c368-40e2-afb9-1104ed95d4ea

-- Generated from ChapterAttentionStreaming.lean — solution of BookProof.ChapterAttentionStreaming.snoc_denom_pos
import Mathlib
import Definitions.Def_ChapterAttentionStreaming
open BookProof.ChapterAttentionStreaming



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta sn : ℝ) (s : Fin m → ℝ) :
    0 < (∑ l, Real.exp (beta * s l)) + Real.exp (beta * sn) := by

  have : (0 : ℝ) ≤ ∑ l, Real.exp (beta * s l) :=
    Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  linarith [Real.exp_pos (beta * sn)]
