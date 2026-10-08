-- Prove2me | solution 1 for BookProof.ChapterA.conjugation_avg_antifixed
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T16:37:54.575124+00:00
-- url     : https://prove2.me/submissions/6f02e5fe-b7c5-41fe-9293-b5a26fb78747

-- Generated from ChapterA1.lean — theorem BookProof.ChapterA.conjugation_avg_antifixed
import Mathlib
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA
open BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

theorem solution (θ : AntiUnitary V) (hθ : ∀ x, θ (θ x) = x) (x : V) :
    θ ((2⁻¹ : ℂ) • (x - θ x)) = -((2⁻¹ : ℂ) • (x - θ x)) := by
  simp [θ.map_smulₛₗ, map_sub, hθ, smul_sub, neg_sub, starRingEnd_apply]

#print axioms solution
