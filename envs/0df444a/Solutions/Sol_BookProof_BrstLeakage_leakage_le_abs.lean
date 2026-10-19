-- Prove2me | solution 1 for BookProof.BrstLeakage.leakage_le_abs
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:46:09.424233+00:00
-- url     : https://prove2.me/submissions/588d508c-32ae-4284-8969-84766288f84e

import Mathlib
import Theorems.Thm_BookProof_BrstLeakage_leakage_le
import Definitions.Def_ChapterBrstTruncationLeakage
-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.leakage_le_abs
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem flow_neg_neg' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (B : E →L[ℂ] E) (s : ℝ) : flow (-B) s = flow B (-s) := by
  unfold flow
  congr 1
  simp only [smul_neg, neg_smul, neg_neg]

theorem solution {H B Om : E →L[ℂ] E} (hH : IsSelfAdjoint H) (hcomm : Commute H Om)
    (t : ℝ) (x : E) (K : ℝ) (hK : ∀ s : ℝ, ‖(H - B) (flow B s x)‖ ≤ K) :
    ‖Om (flow B t x)‖ ≤ ‖Om x‖ + ‖Om‖ * (K * |t|) := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact BookProof.BrstLeakage.leakage_le hH hcomm t ht x K (fun s _ => hK s)
  · rw [abs_of_neg ht]
    have hH' : IsSelfAdjoint (-H) := hH.neg
    have hcomm' : Commute (-H) Om := hcomm.neg_left
    have := BookProof.BrstLeakage.leakage_le (B := -B) hH' hcomm' (-t) (by linarith) x K
      (fun s _ => by
        rw [flow_neg_neg', show -H - -B = -(H - B) by abel, ContinuousLinearMap.neg_apply, norm_neg]
        exact hK (-s))
    rw [flow_neg_neg', neg_neg] at this
    exact this
