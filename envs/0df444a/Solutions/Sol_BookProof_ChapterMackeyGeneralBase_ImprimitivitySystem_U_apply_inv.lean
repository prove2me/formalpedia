-- Prove2me | solution 1 for BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.U_apply_inv
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:36:00.428261+00:00
-- url     : https://prove2.me/submissions/10ddab2d-d410-48ee-88ad-161c8953dbbf

-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.U_apply_inv
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

theorem solution (g : G) (ψ : E) : S.U g (S.U g⁻¹ ψ) = ψ := by
  solve | rfl | simp | omega | norm_num | simp_all
