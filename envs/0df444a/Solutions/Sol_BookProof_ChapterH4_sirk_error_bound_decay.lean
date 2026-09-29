-- Prove2me | solution 1 for BookProof.ChapterH4.sirk_error_bound_decay
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:33:53.85364+00:00
-- url     : https://prove2.me/submissions/e01de78f-0a56-44c4-b0e4-9b4af7b2cca6

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith
set_option autoImplicit false
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

private theorem approximation_bound (V : F →L[ℂ] E) (phiA psiX rX : E →L[ℂ] E) (psiB rB : F →L[ℂ] F)
    (C D : ℝ) (hphi : phiA = psiX)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hrt : ∀ v : E, rX v = V (rB (V.adjoint v)))
    (hcx1 : ‖psiX - rX‖ ≤ C * D) (hcx2 : ‖psiB - rB‖ ≤ C * D) (v : E) :
    ‖phiA v - V (psiB (V.adjoint v))‖ ≤ 2 * C * D * ‖v‖ := by
  rw [hphi]
  have hCD : 0 ≤ C * D := (norm_nonneg _).trans hcx1
  have hfirst : ‖psiX v - rX v‖ ≤ C * D * ‖v‖ := by
    exact ((psiX - rX).le_opNorm v).trans (mul_le_mul_of_nonneg_right hcx1 (norm_nonneg v))
  have hsecond : ‖rX v - V (psiB (V.adjoint v))‖ ≤ C * D * ‖v‖ := by
    calc
      _ = ‖rB (V.adjoint v) - psiB (V.adjoint v)‖ := by rw [hrt, ← map_sub, hViso]
      _ ≤ ‖rB - psiB‖ * ‖V.adjoint v‖ := (rB - psiB).le_opNorm _
      _ ≤ (C * D) * ‖v‖ := by
        rw [norm_sub_rev]
        exact mul_le_mul hcx2 (hVadj v) (norm_nonneg _) hCD
  have htri : ‖psiX v - V (psiB (V.adjoint v))‖ ≤
      ‖psiX v - rX v‖ + ‖rX v - V (psiB (V.adjoint v))‖ := by
    simpa only [dist_eq_norm] using dist_triangle (psiX v) (rX v) (V (psiB (V.adjoint v)))
  nlinarith


theorem solution (V : F →L[ℂ] E) (phiA psiX rX : E →L[ℂ] E) (psiB rB : F →L[ℂ] F)
    (C D Dmin h m : ℝ) (hphi : phiA = psiX)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hrt : ∀ v : E, rX v = V (rB (V.adjoint v)))
    (hcx1 : ‖psiX - rX‖ ≤ C * D) (hcx2 : ‖psiB - rB‖ ≤ C * D)
    (hC : 0 ≤ C) (hdecay : D ≤ Real.exp (-(h * m)) * Dmin) (v : E) :
    ‖phiA v - V (psiB (V.adjoint v))‖ ≤ 2 * C * Real.exp (-(h * m)) * Dmin * ‖v‖ := by
  apply (approximation_bound V phiA psiX rX psiB rB C D hphi hViso hVadj hrt hcx1 hcx2 v).trans
  have hc2 : 0 ≤ 2 * C := mul_nonneg (by norm_num) hC
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdecay hc2) (norm_nonneg v)
  nlinarith
#print axioms solution
