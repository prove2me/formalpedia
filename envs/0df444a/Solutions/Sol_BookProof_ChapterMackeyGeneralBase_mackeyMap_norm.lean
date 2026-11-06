-- Prove2me | solution 1 for BookProof.ChapterMackeyGeneralBase.mackeyMap_norm
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:58:12.710806+00:00
-- url     : https://prove2.me/submissions/80624fe1-fa95-4696-b2da-9ead802baffe

-- ID: 9184f242-ec1f-4ff6-904e-fed3adca112f | NAME: BookProof.ChapterMackeyGeneralBase.mackeyMap_norm | 未本地编译验证
-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.mackeyMap_norm
import Definitions.Def_ChapterOrthogonalSums
import Mathlib
import Definitions.Def_ChapterMackeyGeneralBase
import Definitions.Def_ChapterMackeyImprimitivity
import Definitions.Def_ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity


open scoped InnerProductSpace


open BookProof.ChapterOrthogonalSums

variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (S : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem G X E)
variable (S : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem G X E) (x₀ : X) (s : X → G)
variable {S x₀ s}

theorem solution (ψ : E) (x : X) : ‖BookProof.ChapterMackeyGeneralBase.mackeyMap S s ψ x‖ = ‖S.p x ψ‖ := by
  simp [BookProof.ChapterMackeyGeneralBase.mackeyMap]
