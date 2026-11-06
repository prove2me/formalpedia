-- Prove2me | solution 1 for BookProof.ChapterMackeyGeneralBase.mackeyMap_smul
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:54:37.745143+00:00
-- url     : https://prove2.me/submissions/969fda4f-e060-499f-aa7e-6b20a1baa837

-- ID: b1a105db-0544-4ac4-8a80-8c158ee99943 | NAME: BookProof.ChapterMackeyGeneralBase.mackeyMap_smul | 未本地编译验证
-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.mackeyMap_smul
import Definitions.Def_ChapterOrthogonalSums
import Mathlib
import Definitions.Def_ChapterMackeyGeneralBase
import Definitions.Def_ChapterMackeyImprimitivity
import Definitions.Def_ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity


open scoped InnerProductSpace


open BookProof.ChapterOrthogonalSums

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (S : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem G X E)
variable (S : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem G X E) (x₀ : X) (s : X → G)
variable {S x₀ s}

theorem solution (a : ℂ) (ψ : E) : BookProof.ChapterMackeyGeneralBase.mackeyMap S s (a • ψ) = a • BookProof.ChapterMackeyGeneralBase.mackeyMap S s ψ := by
  funext x
  simp [BookProof.ChapterMackeyGeneralBase.mackeyMap]
