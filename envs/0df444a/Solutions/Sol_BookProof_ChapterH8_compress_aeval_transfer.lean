-- Prove2me | solution 1 for BookProof.ChapterH8.compress_aeval_transfer
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T17:53:21.106986+00:00
-- url     : https://prove2.me/submissions/541d180b-2d1b-45fc-b67c-3e345eb9ce61

-- Generated from ChapterH8.lean — solution of BookProof.ChapterH8.compress_aeval_transfer
import Mathlib
import Definitions.Def_ChapterH8
import Theorems.Thm_BookProof_ChapterH8_compress_aeval_comp
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH4
open BookProof.ChapterH8



open ContinuousLinearMap

noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open BookProof.ChapterH4

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hVV : (adjoint V).comp V = ContinuousLinearMap.id ℂ F)
    (hinv : ∀ x : F, ∃ y : F, X (V x) = V y) (p : Polynomial ℂ)
    (v : E) (hv : V ((adjoint V) v) = v) :
    (Polynomial.aeval X p) v = V ((Polynomial.aeval (compress V X) p) ((adjoint V) v)) := by

  have h := congrArg (fun f : F →L[ℂ] E => f ((adjoint V) v))
    (compress_aeval_comp V X hVV hinv p)
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at h
  rw [hv] at h
  exact h
