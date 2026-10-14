-- Prove2me | solution 1 for BookProof.ChapterMackeyImprimitivity.mackeyMap_intertwines_pvm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:03:43.750209+00:00
-- url     : https://prove2.me/submissions/956ee884-02a8-442f-aebd-2603434f6e51

-- Generated from ChapterMackeyImprimitivity.lean — solution of BookProof.ChapterMackeyImprimitivity.mackeyMap_intertwines_pvm
import Mathlib
import Definitions.Def_ChapterMackeyImprimitivity
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
theorem solution [DecidableEq X] (y : X) (ψ : E) :
    mackeyMap S s (S.p y ψ) = inducedPvm y (mackeyMap S s ψ) := by

  funext x
  by_cases hxy : x = y
  · subst hxy
    simp [mackeyMap, inducedPvm, S.idem]
  · simp [mackeyMap, inducedPvm, hxy, S.orthogonal x y hxy]
