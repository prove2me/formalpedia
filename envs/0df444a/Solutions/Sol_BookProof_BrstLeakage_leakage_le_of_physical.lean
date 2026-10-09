-- Prove2me | solution 1 for BookProof.BrstLeakage.leakage_le_of_physical
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:44:36.059773+00:00
-- url     : https://prove2.me/submissions/adbc99c3-8f18-462a-aba5-4dcdd036e14c

-- Generated from ChapterBrstTruncationLeakage.lean — solution of BookProof.BrstLeakage.leakage_le_of_physical
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
import Theorems.Thm_BookProof_BrstLeakage_leakage_le
open BookProof.BrstLeakage



open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {H B Om : E →L[ℂ] E} (hH : IsSelfAdjoint H)
    (hcomm : Commute H Om) (t : ℝ) (ht : 0 ≤ t) {x : E} (hx : Om x = 0) (K : ℝ)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖(H - B) (flow B s x)‖ ≤ K) :
    ‖Om (flow B t x)‖ ≤ ‖Om‖ * (K * t) := by

  simpa [hx] using leakage_le hH hcomm t ht x K hK
