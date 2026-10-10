-- Prove2me | solution 1 for BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.U_inv_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:30:15.650984+00:00
-- url     : https://prove2.me/submissions/c671f300-508a-4473-9e26-112c0cc8615b

-- Generated from ChapterMackeyImprimitivity.lean — solution of BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.U_inv_apply
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
theorem solution (g : G) (ψ : E) : S.U g⁻¹ (S.U g ψ) = ψ := by

  have h : S.U g⁻¹ (S.U g ψ) = S.U (g⁻¹ * g) ψ := by rw [map_mul]; rfl
  rw [h, inv_mul_cancel, map_one]
  rfl
