-- Prove2me | solution 1 for BookProof.ChapterMackeyGeneralBase.mackeyMap_mem_inducedSpace
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T20:32:16.152087+00:00
-- url     : https://prove2.me/submissions/b9c3a273-ec39-4e5d-a1a0-f11ee5033447

-- Generated from ChapterMackeyGeneralBase.lean — solution of BookProof.ChapterMackeyGeneralBase.mackeyMap_mem_inducedSpace
import Mathlib
import Definitions.Def_ChapterMackeyGeneralBase
import Theorems.Thm_BookProof_ChapterMackeyGeneralBase_mackeyMap_eq
import Theorems.Thm_BookProof_ChapterMackeyGeneralBase_mackeyMap_hasSum_norm_sq
import Theorems.Thm_BookProof_ChapterPvmMeasure_Pvm_idem
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
theorem solution (hs : ∀ x, s x • x₀ = x) (ψ : E) :
    mackeyMap S s ψ ∈ InducedSpace S x₀ := by

  refine ⟨fun x => ?_, (mackeyMap_hasSum_norm_sq (S := S) (s := s) ψ).summable⟩
  rw [mackeyMap_eq hs, S.idem]
