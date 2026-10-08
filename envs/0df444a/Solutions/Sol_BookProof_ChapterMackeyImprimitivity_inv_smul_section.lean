-- Prove2me | solution 1 for BookProof.ChapterMackeyImprimitivity.inv_smul_section
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T14:06:53.164183+00:00
-- url     : https://prove2.me/submissions/2bc29037-a06f-49d9-85f9-e742ce4b97b0

-- Generated from ChapterMackeyImprimitivity.lean — solution of BookProof.ChapterMackeyImprimitivity.inv_smul_section
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
theorem solution (hs : ∀ x, s x • x₀ = x) (x : X) : (s x)⁻¹ • x = x₀ :=
  calc (s x)⁻¹ • x = (s x)⁻¹ • (s x • x₀) := by rw [hs x]
      _ = x₀ := inv_smul_smul _ _
