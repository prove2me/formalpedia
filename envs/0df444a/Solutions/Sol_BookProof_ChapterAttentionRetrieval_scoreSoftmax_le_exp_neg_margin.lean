-- Prove2me | solution 1 for BookProof.ChapterAttentionRetrieval.scoreSoftmax_le_exp_neg_margin
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:38:03.855095+00:00
-- url     : https://prove2.me/submissions/594e8e7b-84e3-467d-9f95-6272d995fb7a

-- Generated from ChapterAttentionRetrieval.lean — solution of BookProof.ChapterAttentionRetrieval.scoreSoftmax_le_exp_neg_margin
import Mathlib
import Definitions.Def_ChapterAttentionRetrieval
import Theorems.Thm_BookProof_ChapterAttentionRetrieval_exp_le_denom
open BookProof.ChapterAttentionRetrieval



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {beta delta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ)
    {j l : Fin m} (h : s l + delta ≤ s j) :
    scoreSoftmax beta s l ≤ Real.exp (-(beta * delta)) := by

  have hZ : Real.exp (beta * s j) ≤ ∑ i, Real.exp (beta * s i) := exp_le_denom beta s j
  have hpos : (0 : ℝ) < Real.exp (beta * s j) := Real.exp_pos _
  have hstep : scoreSoftmax beta s l ≤ Real.exp (beta * s l) / Real.exp (beta * s j) :=
    div_le_div_of_nonneg_left (Real.exp_pos _).le hpos hZ
  have hexp : Real.exp (beta * s l) / Real.exp (beta * s j)
      = Real.exp (beta * s l - beta * s j) := (Real.exp_sub _ _).symm
  have hle : beta * s l - beta * s j ≤ -(beta * delta) := by
    have : beta * delta ≤ beta * (s j - s l) := by
      have hd : delta ≤ s j - s l := by linarith
      exact mul_le_mul_of_nonneg_left hd hb
    nlinarith
  calc scoreSoftmax beta s l ≤ Real.exp (beta * s l - beta * s j) := by rw [← hexp]; exact hstep
    _ ≤ Real.exp (-(beta * delta)) := Real.exp_le_exp.2 hle
