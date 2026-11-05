-- Prove2me | solution 1 for BookProof.ChapterMackeyGeneralBase.mackeyMap_intertwines_pvm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T20:31:25.519372+00:00
-- url     : https://prove2.me/submissions/b0b6dcf7-e8aa-44b7-b158-c44b04672d60

-- Generated from ChapterMackeyGeneralBase.lean — solution of BookProof.ChapterMackeyGeneralBase.mackeyMap_intertwines_pvm
import Mathlib
import Definitions.Def_ChapterMackeyGeneralBase
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
theorem solution [DecidableEq X] (y : X) (ψ : E) :
    mackeyMap S s (S.p y ψ) = inducedPvm y (mackeyMap S s ψ) := by

  funext x
  by_cases hxy : x = y
  · subst hxy
    simp [mackeyMap, inducedPvm, S.idem]
  · simp [mackeyMap, inducedPvm, hxy, S.orthogonal x y hxy]
