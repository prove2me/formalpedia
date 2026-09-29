-- Prove2me | solution 1 for BookProof.ChapterH4.sirk_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:33:52.347199+00:00
-- url     : https://prove2.me/submissions/c7e8ec14-4754-49f8-8363-69b678499d34

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith
set_option autoImplicit false
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem solution (V : F →L[ℂ] E) (phiA psiX rX : E →L[ℂ] E) (psiB rB : F →L[ℂ] F)
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
#print axioms solution
