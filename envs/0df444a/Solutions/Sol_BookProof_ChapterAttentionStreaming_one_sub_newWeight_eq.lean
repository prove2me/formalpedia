-- Prove2me | solution 1 for BookProof.ChapterAttentionStreaming.one_sub_newWeight_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:43:38.841047+00:00
-- url     : https://prove2.me/submissions/01e23d67-1267-4008-8bd9-1548a7f04244

-- Generated from ChapterAttentionStreaming.lean — solution of BookProof.ChapterAttentionStreaming.one_sub_newWeight_eq
import Mathlib
import Definitions.Def_ChapterAttentionStreaming
import Theorems.Thm_BookProof_ChapterAttentionStreaming_newWeight_eq
open BookProof.ChapterAttentionStreaming



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta sn : ℝ) (s : Fin m → ℝ) :
    1 - newWeight beta sn s
      = (∑ l, Real.exp (beta * s l))
          / ((∑ l, Real.exp (beta * s l)) + Real.exp (beta * sn)) := by

  rw [newWeight_eq]
  field_simp
  ring
