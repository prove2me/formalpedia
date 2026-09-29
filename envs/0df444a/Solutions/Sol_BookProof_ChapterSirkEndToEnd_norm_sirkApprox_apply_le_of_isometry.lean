-- Prove2me | solution 1 for BookProof.ChapterSirkEndToEnd.norm_sirkApprox_apply_le_of_isometry
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:17:34.451281+00:00
-- url     : https://prove2.me/submissions/1151569e-5788-4c3f-8a4c-135c8eb4f4db

-- Generated from ChapterSirkEndToEnd.lean — solution of BookProof.ChapterSirkEndToEnd.norm_sirkApprox_apply_le_of_isometry
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
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hpsi : ∀ y : F, ‖psiB y‖ = ‖y‖) (v : E) :
    ‖sirkApprox V psiB v‖ ≤ ‖v‖ := by

  rw [sirkApprox_apply, hViso, hpsi]
  exact hVadj v
