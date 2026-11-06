-- Prove2me | solution 1 for BookProof.ChapterMackeyGeneralBase.mackeyMap_intertwines_U
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T20:32:11.460409+00:00
-- url     : https://prove2.me/submissions/2a7f8c47-2f06-4038-91ad-5b62b5e426ec

-- Generated from ChapterMackeyGeneralBase.lean — solution of BookProof.ChapterMackeyGeneralBase.mackeyMap_intertwines_U
import Mathlib
import Definitions.Def_ChapterMackeyGeneralBase
import Theorems.Thm_BookProof_ChapterMackeyGeneralBase_ImprimitivitySystem_U_mul_apply
import Theorems.Thm_BookProof_ChapterMackeyGeneralBase_mackeyMap_eq
import Theorems.Thm_BookProof_ChapterMackeyGeneralBase_cocycle_mem_stabilizer
import Theorems.Thm_BookProof_ChapterMackeyGeneralBase_stabilizer_comm_fibre
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
theorem solution (hs : ∀ x, s x • x₀ = x) (g : G) (ψ : E) :
    mackeyMap S s (S.U g ψ) = inducedRep S s g (mackeyMap S s ψ) := by

  funext x
  rw [mackeyMap_eq hs, inducedRep, mackeyMap_eq hs,
    stabilizer_comm_fibre (cocycle_mem_stabilizer hs g x), S.U_mul_apply, S.U_mul_apply]
  congr 2
  rw [cocycle]
  group
