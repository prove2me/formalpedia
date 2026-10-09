-- Prove2me | solution 1 for BookProof.ChapterAttentionStreaming.scoreSoftmax_snoc_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:43:43.537094+00:00
-- url     : https://prove2.me/submissions/08ffdf1a-6809-4df1-8a35-8ecf5a3a988a

-- Generated from ChapterAttentionStreaming.lean — solution of BookProof.ChapterAttentionStreaming.scoreSoftmax_snoc_castSucc
import Mathlib
import Definitions.Def_ChapterAttentionStreaming
import Theorems.Thm_BookProof_ChapterAttentionStreaming_snoc_denom
import Theorems.Thm_BookProof_ChapterAttentionStreaming_one_sub_newWeight_eq
open BookProof.ChapterAttentionStreaming



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta sn : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax beta (Fin.snoc s sn) j.castSucc
      = (1 - newWeight beta sn s) * scoreSoftmax beta s j := by

  have hZ : 0 < ∑ l, Real.exp (beta * s l) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨j, Finset.mem_univ j⟩
  rw [one_sub_newWeight_eq, scoreSoftmax, scoreSoftmax, snoc_denom, div_mul_div_comm,
    Fin.snoc_castSucc, mul_comm (∑ l, Real.exp (beta * s l)) (Real.exp (beta * s j)),
    mul_div_mul_right _ _ hZ.ne']
