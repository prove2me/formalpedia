-- Prove2me | solution 1 for BookProof.ChapterAttentionStreaming.snoc_denom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:42:13.06062+00:00
-- url     : https://prove2.me/submissions/377f4923-97c2-4ac1-a9b7-519b8ced0536

-- Generated from ChapterAttentionStreaming.lean — solution of BookProof.ChapterAttentionStreaming.snoc_denom
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
    ∑ l, Real.exp (beta * (Fin.snoc s sn : Fin (m + 1) → ℝ) l)
      = (∑ l, Real.exp (beta * s l)) + Real.exp (beta * sn) := by

  rw [Fin.sum_univ_castSucc]
  simp
