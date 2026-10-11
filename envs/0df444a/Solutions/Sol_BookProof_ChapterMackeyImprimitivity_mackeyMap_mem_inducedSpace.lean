-- Prove2me | solution 1 for BookProof.ChapterMackeyImprimitivity.mackeyMap_mem_inducedSpace
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:03:42.619886+00:00
-- url     : https://prove2.me/submissions/392dcd34-bb0f-473f-b2ea-a893593fc146
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterMackeyImprimitivity.lean — solution of BookProof.ChapterMackeyImprimitivity.mackeyMap_mem_inducedSpace
import Mathlib
import Definitions.Def_ChapterMackeyImprimitivity
import Theorems.Thm_BookProof_ChapterMackeyImprimitivity_mackeyMap_eq
import Theorems.Thm_BookProof_ChapterPvmMeasure_Pvm_idem
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
theorem solution (hs : ∀ x, s x • x₀ = x) (ψ : E) :
    mackeyMap S s ψ ∈ InducedSpace S x₀ := by

  intro x
  rw [mackeyMap_eq hs, S.idem]
