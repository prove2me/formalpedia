-- Prove2me | solution 1 for BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.pvm_parseval
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:03:41.699995+00:00
-- url     : https://prove2.me/submissions/8776b721-3251-4c3c-b1a8-b3bffe49f243

-- Generated from ChapterMackeyImprimitivity.lean — solution of BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.pvm_parseval
import Mathlib
import Definitions.Def_ChapterMackeyImprimitivity
import Theorems.Thm_BookProof_ChapterMackeyImprimitivity_sum_norm_sq_of_orthogonal
import Theorems.Thm_BookProof_QgOuterFockFL_Comparison_selfAdjoint
import Definitions.Def_ChapterStoneConverse
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
theorem solution (ψ : E) : ∑ x : X, ‖S.p x ψ‖ ^ 2 = ‖ψ‖ ^ 2 :=
  sum_norm_sq_of_orthogonal (S.complete ψ) (by
      intro x y hxy
      rw [S.selfAdjoint x ψ (S.p y ψ), S.orthogonal x y hxy, inner_zero_right])
