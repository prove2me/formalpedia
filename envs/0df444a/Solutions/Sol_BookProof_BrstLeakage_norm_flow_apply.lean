-- Prove2me | solution 1 for BookProof.BrstLeakage.norm_flow_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:44:26.93006+00:00
-- url     : https://prove2.me/submissions/473d5fd1-23bd-4237-8db1-cf0abbfb401f

-- Generated from ChapterBrstTruncationLeakage.lean — solution of BookProof.BrstLeakage.norm_flow_apply
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
import Theorems.Thm_BookProof_BrstLeakage_flow_mem_unitary
import Theorems.Thm_BookProof_BrstLeakage_norm_unitary_apply
open BookProof.BrstLeakage



open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) (t : ℝ) (x : E) :
    ‖flow A t x‖ = ‖x‖ := norm_unitary_apply (flow_mem_unitary hA t) x
