-- Prove2me | solution 1 for BookProof.ChapterAttentionStreaming.newWeight_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:43:19.625471+00:00
-- url     : https://prove2.me/submissions/541fcbca-9b1c-4e0f-bd71-9b06c8e55ded

-- Generated from ChapterAttentionStreaming.lean — solution of BookProof.ChapterAttentionStreaming.newWeight_pos
import Mathlib
import Definitions.Def_ChapterAttentionStreaming
import Theorems.Thm_BookProof_ChapterAttentionStreaming_snoc_denom_pos
import Theorems.Thm_BookProof_ChapterAttentionStreaming_newWeight_eq
open BookProof.ChapterAttentionStreaming



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta sn : ℝ) (s : Fin m → ℝ) : 0 < newWeight beta sn s := by

  rw [newWeight_eq]
  exact div_pos (Real.exp_pos _) (snoc_denom_pos beta sn s)
