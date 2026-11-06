-- Prove2me | solution 1 for BookProof.ChapterMackeyGeneralBase.mackeyMap_reconstruct
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:55:55.412869+00:00
-- url     : https://prove2.me/submissions/5cbfd2a1-81d4-407f-a27b-762913e6aac8

-- ID: 6fbc7945-caa4-4a14-8b58-a9ba9747db55 | NAME: BookProof.ChapterMackeyGeneralBase.mackeyMap_reconstruct | 未本地编译验证
-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.mackeyMap_reconstruct
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

theorem solution (ψ : E) :
    HasSum (fun x => S.U (s x) (BookProof.ChapterMackeyGeneralBase.mackeyMap S s ψ x)) ψ := by
  simpa [BookProof.ChapterMackeyGeneralBase.mackeyMap] using S.complete ψ
