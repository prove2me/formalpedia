-- Prove2me | solution 1 for BookProof.ChapterMackeyGeneralBase.mackeyMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T20:32:01.661755+00:00
-- url     : https://prove2.me/submissions/d64460df-8f7f-4b81-b111-29c8ed980e47

-- Generated from ChapterMackeyGeneralBase.lean — solution of BookProof.ChapterMackeyGeneralBase.mackeyMap_injective
import Mathlib
import Definitions.Def_ChapterMackeyGeneralBase
import Theorems.Thm_BookProof_ChapterMackeyGeneralBase_mackeyMap_reconstruct
open BookProof.ChapterMackeyGeneralBase



open scoped InnerProductSpace


open BookProof.ChapterOrthogonalSums

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (S : ImprimitivitySystem G X E)
variable (S : ImprimitivitySystem G X E) (x₀ : X) (s : X → G)
variable {S x₀ s}

set_option maxHeartbeats 1000000 in
theorem solution : Function.Injective (mackeyMap S s) := by

  intro ψ φ h
  have h1 : HasSum (fun x => S.U (s x) (mackeyMap S s ψ x)) ψ := mackeyMap_reconstruct ψ
  have h2 : HasSum (fun x => S.U (s x) (mackeyMap S s φ x)) φ := mackeyMap_reconstruct φ
  rw [h] at h1
  exact h1.unique h2
