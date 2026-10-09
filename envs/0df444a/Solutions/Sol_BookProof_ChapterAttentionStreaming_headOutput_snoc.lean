-- Prove2me | solution 1 for BookProof.ChapterAttentionStreaming.headOutput_snoc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:44:02.594157+00:00
-- url     : https://prove2.me/submissions/eea26325-9c4d-4081-8d0a-2c5a5a3820db

-- Generated from ChapterAttentionStreaming.lean — solution of BookProof.ChapterAttentionStreaming.headOutput_snoc
import Mathlib
import Definitions.Def_ChapterAttentionStreaming
import Theorems.Thm_BookProof_ChapterAttentionStreaming_scoreSoftmax_snoc_castSucc
import Theorems.Thm_BookProof_ChapterAttentionOutput_headOutput_eq_sum
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterAttentionOutput
open BookProof.ChapterAttentionStreaming



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta sn : ℝ) (s : Fin m → ℝ) (vn : E) (v : Fin m → E) :
    headOutput beta (Fin.snoc s sn) (Fin.snoc v vn)
      = (1 - newWeight beta sn s) • headOutput beta s v + newWeight beta sn s • vn := by

  rw [headOutput_eq_sum, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  congr 1
  calc ∑ j, scoreSoftmax beta (Fin.snoc s sn) j.castSucc • v j
      = ∑ j, ((1 - newWeight beta sn s) * scoreSoftmax beta s j) • v j :=
        Finset.sum_congr rfl fun j _ => by rw [scoreSoftmax_snoc_castSucc]
    _ = (1 - newWeight beta sn s) • ∑ j, scoreSoftmax beta s j • v j := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [mul_smul]
    _ = (1 - newWeight beta sn s) • headOutput beta s v := rfl
