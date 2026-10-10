-- Prove2me | solution 1 for BookProof.ChapterH8.compress_aeval_comp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T17:52:45.325957+00:00
-- url     : https://prove2.me/submissions/7e39a62a-297f-4b99-965b-0718aa854f5f

-- Generated from ChapterH8.lean — solution of BookProof.ChapterH8.compress_aeval_comp
import Mathlib
import Definitions.Def_ChapterH8
import Theorems.Thm_BookProof_ChapterH4_compress_pow
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
    (hinv : ∀ x : F, ∃ y : F, X (V x) = V y) (p : Polynomial ℂ) :
    (Polynomial.aeval X p).comp V = V.comp (Polynomial.aeval (compress V X) p) := by

  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [map_add, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hp, hq]
  | monomial k c =>
      have h := compress_pow V X hVV hinv k
      ext x
      have hx := congrArg (fun f : F →L[ℂ] E => f x) h
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at hx
      simp only [Polynomial.aeval_monomial, ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.mul_apply]
      rw [hx]
      simp [Algebra.algebraMap_eq_smul_one]
