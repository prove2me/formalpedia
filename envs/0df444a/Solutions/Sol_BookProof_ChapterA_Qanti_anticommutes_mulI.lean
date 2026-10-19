-- Prove2me | solution 1 for BookProof.ChapterA.Qanti_anticommutes_mulI
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:47:09.357576+00:00
-- url     : https://prove2.me/submissions/eeb1e794-dd4f-4afd-a028-79d4d00987ca

-- Generated from ChapterA2c.lean — solution of BookProof.ChapterA.Qanti_anticommutes_mulI
import Mathlib
import Definitions.Def_ChapterA2c
import Theorems.Thm_BookProof_ChapterA_Qanti_mulI_comm
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (S : V →L[ℝ] V) (x : V) :
    Qanti S (Complex.I • x) = -(Complex.I • Qanti S x) := by

  have h2 := congr_arg (fun T => T x) (Qanti_mulI_comm S)
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.neg_apply, mulI_apply] at h2
  rw [h2, neg_neg]
