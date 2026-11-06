-- Prove2me | solution 1 for BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.U_inv_apply
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:34:07.568264+00:00
-- url     : https://prove2.me/submissions/268db2f0-2658-4a8c-a773-92ff83ff6b7c

-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.U_inv_apply
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

theorem solution (g : G) (ψ : E) : S.U g⁻¹ (S.U g ψ) = ψ := by
  solve | rfl | simp | omega | norm_num | simp_all
