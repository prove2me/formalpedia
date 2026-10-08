-- Prove2me | solution 1 for BookProof.ChapterA.rimaginary_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T16:37:56.713994+00:00
-- url     : https://prove2.me/submissions/7ec511eb-a12f-4ae6-9cdd-a51fe6b09ed7

-- Generated from ChapterA1.lean — theorem BookProof.ChapterA.rimaginary_symm_apply
import Mathlib
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA
open BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

theorem solution (J : W ≃ₗᵢ[ℝ] W) (hJ : ∀ x, J (J x) = -x) (x : W) :
    J.symm x = -J x := by
  apply J.injective
  simp [hJ]

#print axioms solution
