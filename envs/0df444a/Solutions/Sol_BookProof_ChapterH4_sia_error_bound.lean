-- Prove2me | solution 1 for BookProof.ChapterH4.sia_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:33:53.138784+00:00
-- url     : https://prove2.me/submissions/39cef88a-c9e6-437e-bffe-ecafe4182666

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith
set_option autoImplicit false
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem solution (V : F →L[ℂ] E) (phiA psiX pX : E →L[ℂ] E) (psiB pB : F →L[ℂ] F)
    (C Dsia : ℝ) (hphi : phiA = psiX)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hrt : ∀ v : E, pX v = V (pB (V.adjoint v)))
    (hcx1 : ‖psiX - pX‖ ≤ C * Dsia) (hcx2 : ‖psiB - pB‖ ≤ C * Dsia) (v : E) :
    ‖phiA v - V (psiB (V.adjoint v))‖ ≤ 2 * C * Dsia * ‖v‖ := by
  rw [hphi]
  have hCD : 0 ≤ C * Dsia := (norm_nonneg _).trans hcx1
  have hfirst : ‖psiX v - pX v‖ ≤ C * Dsia * ‖v‖ := by
    exact ((psiX - pX).le_opNorm v).trans (mul_le_mul_of_nonneg_right hcx1 (norm_nonneg v))
  have hsecond : ‖pX v - V (psiB (V.adjoint v))‖ ≤ C * Dsia * ‖v‖ := by
    calc
      _ = ‖pB (V.adjoint v) - psiB (V.adjoint v)‖ := by rw [hrt, ← map_sub, hViso]
      _ ≤ ‖pB - psiB‖ * ‖V.adjoint v‖ := (pB - psiB).le_opNorm _
      _ ≤ (C * Dsia) * ‖v‖ := by
        rw [norm_sub_rev]
        exact mul_le_mul hcx2 (hVadj v) (norm_nonneg _) hCD
  have htri : ‖psiX v - V (psiB (V.adjoint v))‖ ≤
      ‖psiX v - pX v‖ + ‖pX v - V (psiB (V.adjoint v))‖ := by
    simpa only [dist_eq_norm] using dist_triangle (psiX v) (pX v) (V (psiB (V.adjoint v)))
  nlinarith
#print axioms solution
