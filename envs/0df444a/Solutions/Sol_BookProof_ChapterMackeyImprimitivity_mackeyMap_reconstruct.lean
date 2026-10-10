-- Prove2me | solution 1 for BookProof.ChapterMackeyImprimitivity.mackeyMap_reconstruct
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:32:21.070953+00:00
-- url     : https://prove2.me/submissions/7d76ce62-fb9e-4f8a-a710-9f174dae9244

-- Generated from ChapterMackeyImprimitivity.lean — solution of BookProof.ChapterMackeyImprimitivity.mackeyMap_reconstruct
import Mathlib
import Definitions.Def_ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity



open scoped InnerProductSpace
open Finset


variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (S : ImprimitivitySystem G X E)
variable (S : ImprimitivitySystem G X E) (x₀ : X) (s : X → G)
variable {S x₀ s}

set_option maxHeartbeats 1000000 in
theorem solution (ψ : E) : ∑ x : X, S.U (s x) (mackeyMap S s ψ x) = ψ := by

  have : ∀ x : X, S.U (s x) (mackeyMap S s ψ x) = S.p x ψ := by
    intro x
    simp [mackeyMap]
  simp only [this]
  exact S.complete ψ
