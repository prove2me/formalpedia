-- Prove2me | solution 1 for BookProof.ChapterMackeyImprimitivity.mackeyMap_intertwines_U
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:34:35.505656+00:00
-- url     : https://prove2.me/submissions/4fe6f82b-6b1d-4806-822a-e57961130382

-- Generated from ChapterMackeyImprimitivity.lean — solution of BookProof.ChapterMackeyImprimitivity.mackeyMap_intertwines_U
import Mathlib
import Definitions.Def_ChapterMackeyImprimitivity
import Theorems.Thm_BookProof_ChapterMackeyImprimitivity_ImprimitivitySystem_U_mul_apply
import Theorems.Thm_BookProof_ChapterMackeyImprimitivity_mackeyMap_eq
import Theorems.Thm_BookProof_ChapterMackeyImprimitivity_cocycle_mem_stabilizer
import Theorems.Thm_BookProof_ChapterMackeyImprimitivity_stabilizer_comm_fibre
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
theorem solution (hs : ∀ x, s x • x₀ = x) (g : G) (ψ : E) :
    mackeyMap S s (S.U g ψ) = inducedRep S s g (mackeyMap S s ψ) := by

  funext x
  rw [mackeyMap_eq hs, inducedRep, mackeyMap_eq hs,
    stabilizer_comm_fibre (cocycle_mem_stabilizer hs g x), S.U_mul_apply, S.U_mul_apply]
  congr 2
  rw [cocycle]
  group
