-- Prove2me | solution 1 for BookProof.ChapterSirkEndToEnd.sirk_error_bound_at
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T03:55:33.441102+00:00
-- url     : https://prove2.me/submissions/d38bba80-ab71-429b-a8ed-b71ca8c74760

-- Generated from ChapterSirkEndToEnd.lean — solution of BookProof.ChapterSirkEndToEnd.sirk_error_bound_at
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
theorem solution
    (V : F →L[ℂ] E) (phiA psiX rX : E →L[ℂ] E) (psiB rB : F →L[ℂ] F)
    (C D : ℝ)
    (hphi : phiA = psiX)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hcx1 : ‖psiX - rX‖ ≤ C * D)
    (hcx2 : ‖psiB - rB‖ ≤ C * D)
    (v : E) (hrt : rX v = V (rB (V.adjoint v))) :
    ‖phiA v - sirkApprox V psiB v‖ ≤ 2 * C * D * ‖v‖ := by

  have hCD : 0 ≤ C * D := le_trans (norm_nonneg _) hcx2
  have key : phiA v - sirkApprox V psiB v
      = (psiX - rX) v + V ((rB - psiB) (V.adjoint v)) := by
    have h1 : V ((rB - psiB) (V.adjoint v))
        = V (rB (V.adjoint v)) - V (psiB (V.adjoint v)) := by
      rw [ContinuousLinearMap.sub_apply, map_sub]
    rw [h1, ContinuousLinearMap.sub_apply, ← hrt, hphi, sirkApprox_apply]
    abel
  rw [key]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖(psiX - rX) v‖ ≤ C * D * ‖v‖ :=
    le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_right hcx1 (norm_nonneg _))
  have h2 : ‖V ((rB - psiB) (V.adjoint v))‖ ≤ C * D * ‖v‖ := by
    rw [hViso]
    refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
    exact mul_le_mul (by simpa only [norm_sub_rev] using hcx2) (hVadj v) (norm_nonneg _) hCD
  linarith
