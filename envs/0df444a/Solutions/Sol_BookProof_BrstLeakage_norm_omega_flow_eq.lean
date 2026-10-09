-- Prove2me | solution 1 for BookProof.BrstLeakage.norm_omega_flow_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:44:29.219397+00:00
-- url     : https://prove2.me/submissions/765cce3c-d840-4cb9-875b-f092957102ca

-- Generated from ChapterBrstTruncationLeakage.lean — solution of BookProof.BrstLeakage.norm_omega_flow_eq
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
import Theorems.Thm_BookProof_BrstLeakage_norm_flow_apply
import Theorems.Thm_BookProof_BrstLeakage_omega_flow_apply
open BookProof.BrstLeakage



open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {A Om : E →L[ℂ] E} (hA : IsSelfAdjoint A) (h : Commute A Om)
    (t : ℝ) (x : E) : ‖Om (flow A t x)‖ = ‖Om x‖ := by

  rw [omega_flow_apply h t x, norm_flow_apply hA]
