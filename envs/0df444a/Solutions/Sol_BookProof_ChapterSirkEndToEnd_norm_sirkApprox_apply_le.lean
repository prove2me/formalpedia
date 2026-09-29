-- Prove2me | solution 1 for BookProof.ChapterSirkEndToEnd.norm_sirkApprox_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:16:15.40704+00:00
-- url     : https://prove2.me/submissions/12e7302f-924f-4263-a59e-9e1d2b1e372b

-- Generated from ChapterSirkEndToEnd.lean — solution of BookProof.ChapterSirkEndToEnd.norm_sirkApprox_apply_le
import Mathlib
import Definitions.Def_ChapterSirkEndToEnd
import Theorems.Thm_BookProof_ChapterSirkEndToEnd_sirkApprox_apply
open BookProof.ChapterSirkEndToEnd











noncomputable section

open Filter Topology


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH8 BookProof.ChapterH9

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (V : F →L[ℂ] E) (psiB : F →L[ℂ] F)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖) (v : E) :
    ‖sirkApprox V psiB v‖ ≤ ‖psiB‖ * ‖v‖ := by

  rw [sirkApprox_apply, hViso]
  exact le_trans (psiB.le_opNorm _)
    (mul_le_mul_of_nonneg_left (hVadj v) (norm_nonneg _))
