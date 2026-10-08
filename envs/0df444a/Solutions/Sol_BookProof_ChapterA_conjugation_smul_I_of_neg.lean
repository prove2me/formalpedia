-- Prove2me | solution 1 for BookProof.ChapterA.conjugation_smul_I_of_neg
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T16:42:43.708091+00:00
-- url     : https://prove2.me/submissions/47584b33-f956-4a8c-959f-fce8c5006750

-- Generated from ChapterA1.lean — theorem BookProof.ChapterA.conjugation_smul_I_of_neg
import Mathlib
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA
open BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

theorem solution (θ : AntiUnitary V) {y : V} (hy : θ y = -y) :
    θ (Complex.I • y) = Complex.I • y := by
  rw [θ.map_smulₛₗ]
  change conj Complex.I • θ y = Complex.I • y
  rw [Complex.conj_I, hy]
  simp only [neg_smul, smul_neg, neg_neg]

#print axioms solution
