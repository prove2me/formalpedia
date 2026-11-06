-- Prove2me | solution 1 for BookProof.ChapterMackeyGeneralBase.mackeyMap_add
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:58:24.078512+00:00
-- url     : https://prove2.me/submissions/80b63533-3399-42ad-ac81-e26d2b5aa6b2

-- ID: ea37f513-b52a-4d22-8806-38fb31d4dc14 | NAME: BookProof.ChapterMackeyGeneralBase.mackeyMap_add | 未本地编译验证
-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.mackeyMap_add
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

theorem solution (ψ φ : E) : BookProof.ChapterMackeyGeneralBase.mackeyMap S s (ψ + φ) = BookProof.ChapterMackeyGeneralBase.mackeyMap S s ψ + BookProof.ChapterMackeyGeneralBase.mackeyMap S s φ := by
  ext x
  simp [BookProof.ChapterMackeyGeneralBase.mackeyMap]
