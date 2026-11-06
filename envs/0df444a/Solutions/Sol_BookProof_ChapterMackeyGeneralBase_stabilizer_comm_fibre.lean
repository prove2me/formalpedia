-- Prove2me | solution 1 for BookProof.ChapterMackeyGeneralBase.stabilizer_comm_fibre
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:52:44.737864+00:00
-- url     : https://prove2.me/submissions/5aacbead-03cd-455b-aea8-38f8571589ab

-- ID: 793e19c5-fa2b-431c-bcc8-348f50a05eef | NAME: BookProof.ChapterMackeyGeneralBase.stabilizer_comm_fibre | 未本地编译验证
-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.stabilizer_comm_fibre
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

theorem solution {h : G} (hh : h ∈ MulAction.stabilizer G x₀) (v : E) :
    S.U h (S.p x₀ v) = S.p x₀ (S.U h v) := by
  have hfix : h • x₀ = x₀ := by simpa using hh
  simpa [hfix] using S.covariant h x₀ v
