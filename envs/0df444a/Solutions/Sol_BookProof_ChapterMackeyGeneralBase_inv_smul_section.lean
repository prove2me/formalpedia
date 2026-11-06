-- Prove2me | solution 1 for BookProof.ChapterMackeyGeneralBase.inv_smul_section
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:57:42.095281+00:00
-- url     : https://prove2.me/submissions/f987dabc-3851-4f61-b9ea-3c9ec667c08f

-- ID: 1d1355aa-3775-4ae3-af60-8ead253e99ce | NAME: BookProof.ChapterMackeyGeneralBase.inv_smul_section | 未本地编译验证
-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.inv_smul_section
import Definitions.Def_ChapterOrthogonalSums
import Mathlib
import Definitions.Def_ChapterMackeyGeneralBase


open scoped InnerProductSpace


open BookProof.ChapterOrthogonalSums

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (S : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem G X E)
variable (S : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem G X E) (x₀ : X) (s : X → G)
variable {S x₀ s}

theorem solution (hs : ∀ x, s x • x₀ = x) (x : X) : (s x)⁻¹ • x = x₀ := by
  calc
    (s x)⁻¹ • x = (s x)⁻¹ • (s x • x₀) := by rw [hs x]
    _ = x₀ := by simp
