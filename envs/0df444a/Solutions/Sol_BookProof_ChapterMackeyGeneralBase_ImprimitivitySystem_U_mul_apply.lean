-- Prove2me | solution 1 for BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.U_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:38:29.423197+00:00
-- url     : https://prove2.me/submissions/91cacf76-1016-4d16-98fc-f6c8841515da

-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.U_mul_apply
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

theorem solution (g h : G) (ψ : E) : S.U g (S.U h ψ) = S.U (g * h) ψ := by
  solve | rfl | simp | omega | norm_num | simp_all
