-- Prove2me | solution 1 for BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.U_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:30:34.052165+00:00
-- url     : https://prove2.me/submissions/4e325c92-3ab7-4222-be15-eb4acc7846e3

-- Generated from ChapterMackeyImprimitivity.lean — solution of BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.U_mul_apply
import Mathlib
import Definitions.Def_ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem



open scoped InnerProductSpace
open Finset


variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (S : ImprimitivitySystem G X E)

set_option maxHeartbeats 1000000 in
theorem solution (g h : G) (ψ : E) : S.U g (S.U h ψ) = S.U (g * h) ψ := by

  rw [map_mul]; rfl
