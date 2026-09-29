-- Prove2me | solution 1 for BookProof.ChapterSirkTruncation.sirk_end_to_end_truncated_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T19:05:52.210566+00:00
-- url     : https://prove2.me/submissions/57557142-3044-4670-80f2-925c6f5a6dc8

-- Generated from ChapterSirkTruncation.lean — solution of BookProof.ChapterSirkTruncation.sirk_end_to_end_truncated_of_exact
import Mathlib
import Definitions.Def_ChapterSirkTruncation
import Theorems.Thm_BookProof_ChapterSirkTruncation_sirk_end_to_end_truncated
open BookProof.ChapterSirkTruncation









noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterSirkEndToEnd
open BookProof.ChapterSirkWhitening

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

set_option maxHeartbeats 1000000 in
theorem solution
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
