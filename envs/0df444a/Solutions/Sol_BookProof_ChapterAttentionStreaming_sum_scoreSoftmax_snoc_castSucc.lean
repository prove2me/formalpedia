-- Prove2me | solution 1 for BookProof.ChapterAttentionStreaming.sum_scoreSoftmax_snoc_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:47:47.513151+00:00
-- url     : https://prove2.me/submissions/d55867ad-d561-414d-9516-447aca83837c

-- Generated from ChapterAttentionStreaming.lean — solution of BookProof.ChapterAttentionStreaming.sum_scoreSoftmax_snoc_castSucc
import Mathlib
import Definitions.Def_ChapterAttentionStreaming
import Theorems.Thm_BookProof_ChapterAttentionStreaming_scoreSoftmax_snoc_castSucc
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_sum_one
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterAttentionStreaming



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta sn : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    ∑ j : Fin m, scoreSoftmax beta (Fin.snoc s sn) j.castSucc = 1 - newWeight beta sn s := by

  calc ∑ j : Fin m, scoreSoftmax beta (Fin.snoc s sn) j.castSucc
      = ∑ j, (1 - newWeight beta sn s) * scoreSoftmax beta s j :=
        Finset.sum_congr rfl fun j _ => scoreSoftmax_snoc_castSucc beta sn s j
    _ = (1 - newWeight beta sn s) * ∑ j, scoreSoftmax beta s j := by rw [Finset.mul_sum]
    _ = 1 - newWeight beta sn s := by rw [scoreSoftmax_sum_one beta s i, mul_one]
