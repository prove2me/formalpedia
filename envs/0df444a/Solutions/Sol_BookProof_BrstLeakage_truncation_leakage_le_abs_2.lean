-- Prove2me | solution 2 for BookProof.BrstLeakage.truncation_leakage_le_abs
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:46:35.380881+00:00
-- url     : https://prove2.me/submissions/c3662bd3-2200-4296-8ad5-30bcdbab5c1a

import Mathlib
import Theorems.Thm_BookProof_BrstLeakage_truncation_leakage_le
import Definitions.Def_ChapterBrstTruncationLeakage
-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.truncation_leakage_le_abs
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem flow_neg_neg' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (B : E →L[ℂ] E) (s : ℝ) : flow (-B) s = flow B (-s) := by
  unfold flow
  congr 1
  simp only [smul_neg, neg_smul, neg_neg]

theorem solution {P H Om : E →L[ℂ] E} (hPi : IsIdempotentElem P)
    (hPs : IsSelfAdjoint P) (hH : IsSelfAdjoint H) (hcomm : Commute H Om)
    (t : ℝ) {x : E} (hx : P x = x) :
    ‖Om (flow (truncGen P H) t x)‖ ≤ ‖Om x‖ + ‖Om‖ * (‖(1 - P) * H * P‖ * ‖x‖ * |t|) := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact BookProof.BrstLeakage.truncation_leakage_le hPi hPs hH hcomm t ht hx
  · rw [abs_of_neg ht]
    have := BookProof.BrstLeakage.truncation_leakage_le hPi hPs hH.neg hcomm.neg_left (-t)
      (by linarith) hx
    have htg : truncGen P (-H) = -truncGen P H := by
      unfold truncGen; rw [mul_neg, neg_mul]
    rw [htg, flow_neg_neg', neg_neg, show (1 - P) * -H * P = -((1 - P) * H * P) by
      rw [mul_neg, neg_mul], norm_neg] at this
    exact this
