-- Prove2me | solution 1 for BookProof.ChapterMackeyGeneralBase.fibre_stabilizer_invariant
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:54:14.38521+00:00
-- url     : https://prove2.me/submissions/7613d682-6c97-4d32-8a23-8d338ad3f634

-- ID: 2130fd5c-2482-4373-a04f-2134fe5accac | NAME: BookProof.ChapterMackeyGeneralBase.fibre_stabilizer_invariant | 未本地编译验证
-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.fibre_stabilizer_invariant
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

theorem solution {h : G} (hh : h ∈ MulAction.stabilizer G x₀) {v : E}
    (hv : S.p x₀ v = v) : S.p x₀ (S.U h v) = S.U h v := by
  have hfix : h • x₀ = x₀ := by simpa using hh
  have hcov : S.U h (S.p x₀ v) = S.p x₀ (S.U h v) := by
    simpa [hfix] using S.covariant h x₀ v
  rw [hv] at hcov
  exact hcov.symm
