-- Prove2me | solution 1 for BookProof.ChapterSirkTruncation.transfer_defect_le_of_leakage
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:30:22.388312+00:00
-- url     : https://prove2.me/submissions/03f3c4d7-7348-4b5b-9417-d6c4ddfcb91d

import Definitions.Def_ChapterSirkTruncation
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace SirkTruncAux
open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterSirkEndToEnd
open BookProof.ChapterSirkWhitening BookProof.ChapterSirkTruncation
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

@[simp] private theorem sirkApprox_apply (V : F →L[ℂ] E) (psiB : F →L[ℂ] F) (v : E) :
    sirkApprox V psiB v = V (psiB (V.adjoint v)) := rfl

private theorem compress_comp (V : F →L[ℂ] E) (W : G →L[ℂ] F) (X : E →L[ℂ] E) :
    compress (V.comp W) X = compress W (compress V X) := by
  simp [compress, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]

private theorem isometry_comp (V : F →L[ℂ] E) (W : G →L[ℂ] F)
    (hV : ∀ x : F, ‖V x‖ = ‖x‖) (hW : ∀ x : G, ‖W x‖ = ‖x‖) (x : G) :
    ‖(V.comp W) x‖ = ‖x‖ := by
  simp [hV, hW]

private theorem sirk_error_bound_at_leaky
    (V : F →L[ℂ] E) (phiA psiX rX : E →L[ℂ] E) (psiB rB : F →L[ℂ] F)
    (C D rho : ℝ)
    (hphi : phiA = psiX)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hcx1 : ‖psiX - rX‖ ≤ C * D)
    (hcx2 : ‖psiB - rB‖ ≤ C * D)
    (v : E) (hrt : ‖rX v - V (rB (V.adjoint v))‖ ≤ rho) :
    ‖phiA v - sirkApprox V psiB v‖ ≤ 2 * C * D * ‖v‖ + rho := by
  have hCD : 0 ≤ C * D := le_trans (norm_nonneg _) hcx2
  have key : phiA v - sirkApprox V psiB v
      = (psiX - rX) v + (rX v - V (rB (V.adjoint v)))
        + V ((rB - psiB) (V.adjoint v)) := by
    have h1 : V ((rB - psiB) (V.adjoint v))
        = V (rB (V.adjoint v)) - V (psiB (V.adjoint v)) := by
      rw [ContinuousLinearMap.sub_apply, map_sub]
    rw [h1, ContinuousLinearMap.sub_apply, hphi, sirkApprox_apply]
    abel
  rw [key]
  have h1 : ‖(psiX - rX) v‖ ≤ C * D * ‖v‖ :=
    le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_right hcx1 (norm_nonneg _))
  have h2 : ‖V ((rB - psiB) (V.adjoint v))‖ ≤ C * D * ‖v‖ := by
    rw [hViso]
    refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
    exact mul_le_mul (by simpa only [norm_sub_rev] using hcx2) (hVadj v) (norm_nonneg _) hCD
  calc ‖(psiX - rX) v + (rX v - V (rB (V.adjoint v))) + V ((rB - psiB) (V.adjoint v))‖
      ≤ ‖(psiX - rX) v + (rX v - V (rB (V.adjoint v)))‖
        + ‖V ((rB - psiB) (V.adjoint v))‖ := norm_add_le _ _
    _ ≤ (‖(psiX - rX) v‖ + ‖rX v - V (rB (V.adjoint v))‖)
        + ‖V ((rB - psiB) (V.adjoint v))‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ (C * D * ‖v‖ + rho) + C * D * ‖v‖ := by gcongr
    _ = 2 * C * D * ‖v‖ + rho := by ring

private theorem transfer_defect_le_of_leakage (V : F →L[ℂ] E) (rX : E →L[ℂ] E) (rB : F →L[ℂ] F)
    (v : E) (hexact : rX (V (V.adjoint v)) = V (rB (V.adjoint (V (V.adjoint v)))))
    (hproj : V.adjoint (V (V.adjoint v)) = V.adjoint v) :
    ‖rX v - V (rB (V.adjoint v))‖ ≤ ‖rX‖ * ‖v - V (V.adjoint v)‖ := by
  have hw : rX (V (V.adjoint v)) = V (rB (V.adjoint v)) := by rw [hexact, hproj]
  rw [← hw, ← map_sub]
  exact rX.le_opNorm _

private theorem adjoint_reconstruction_eq (V : F →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) (v : E) :
    V.adjoint (V (V.adjoint v)) = V.adjoint v :=
  congrArg (fun f : F →L[ℂ] F => f (V.adjoint v)) hVV

private theorem sirk_end_to_end_truncated
    (V : F →L[ℂ] E) (rX : E →L[ℂ] E) (rB : F →L[ℂ] F)
    (flow psiX : E →L[ℂ] E) (psiB : F →L[ℂ] F) (C Dmin h : ℝ) (m : ℕ)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hflow : flow = psiX)
    (hcx1 : ‖psiX - rX‖ ≤ C * (Real.exp (-(h * m)) * Dmin))
    (hcx2 : ‖psiB - rB‖ ≤ C * (Real.exp (-(h * m)) * Dmin))
    (v : E) (hexact : rX (V (V.adjoint v)) = V (rB (V.adjoint (V (V.adjoint v)))))
    (hproj : V.adjoint (V (V.adjoint v)) = V.adjoint v) :
    ‖flow v - sirkApprox V psiB v‖
      ≤ sirkBound C Dmin h ‖v‖ m
        + ‖rX‖ * ‖v - V (V.adjoint v)‖ := by
  have hdef := transfer_defect_le_of_leakage V rX rB v hexact hproj
  have := sirk_error_bound_at_leaky V flow psiX rX psiB rB C
    (Real.exp (-(h * m)) * Dmin) _ hflow hViso hVadj hcx1 hcx2 v hdef
  simpa [sirkBound, mul_assoc] using this

private theorem sirk_end_to_end_truncated_of_exact
    (V : F →L[ℂ] E) (rX : E →L[ℂ] E) (rB : F →L[ℂ] F)
    (flow psiX : E →L[ℂ] E) (psiB : F →L[ℂ] F) (C Dmin h : ℝ) (m : ℕ)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hflow : flow = psiX)
    (hcx1 : ‖psiX - rX‖ ≤ C * (Real.exp (-(h * m)) * Dmin))
    (hcx2 : ‖psiB - rB‖ ≤ C * (Real.exp (-(h * m)) * Dmin))
    (v : E) (hv : V (V.adjoint v) = v)
    (hexact : rX (V (V.adjoint v)) = V (rB (V.adjoint (V (V.adjoint v)))))
    (hproj : V.adjoint (V (V.adjoint v)) = V.adjoint v) :
    ‖flow v - sirkApprox V psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m := by
  have := sirk_end_to_end_truncated V rX rB flow psiX psiB C Dmin h m
    hViso hVadj hflow hcx1 hcx2 v hexact hproj
  simpa [hv] using this

end SirkTruncAux

-- Generated from ChapterSirkTruncation.lean — theorem BookProof.ChapterSirkTruncation.transfer_defect_le_of_leakage
open BookProof.ChapterSirkTruncation








noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterSirkEndToEnd
open BookProof.ChapterSirkWhitening

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
open SirkTruncAux

theorem solution (V : F →L[ℂ] E) (rX : E →L[ℂ] E) (rB : F →L[ℂ] F)
    (v : E) (hexact : rX (V (V.adjoint v)) = V (rB (V.adjoint (V (V.adjoint v)))))
    (hproj : V.adjoint (V (V.adjoint v)) = V.adjoint v) :
    ‖rX v - V (rB (V.adjoint v))‖ ≤ ‖rX‖ * ‖v - V (V.adjoint v)‖ := by
  have hw : rX (V (V.adjoint v)) = V (rB (V.adjoint v)) := by rw [hexact, hproj]
  rw [← hw, ← map_sub]
  exact rX.le_opNorm _

#print axioms solution
