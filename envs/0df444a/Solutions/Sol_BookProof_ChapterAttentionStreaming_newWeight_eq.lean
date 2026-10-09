-- Prove2me | solution 1 for BookProof.ChapterAttentionStreaming.newWeight_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:43:04.390301+00:00
-- url     : https://prove2.me/submissions/f3f1def1-6761-41f3-ae34-7e1878531bd2

-- Generated from ChapterAttentionStreaming.lean — solution of BookProof.ChapterAttentionStreaming.newWeight_eq
import Mathlib
import Definitions.Def_ChapterAttentionStreaming
import Theorems.Thm_BookProof_ChapterAttentionStreaming_snoc_denom
open BookProof.ChapterAttentionStreaming



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta sn : ℝ) (s : Fin m → ℝ) :
    newWeight beta sn s
      = Real.exp (beta * sn) / ((∑ l, Real.exp (beta * s l)) + Real.exp (beta * sn)) := by

  rw [newWeight, scoreSoftmax, snoc_denom]
  simp
