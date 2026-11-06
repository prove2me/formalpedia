-- Prove2me | solution 2 for BookProof.ChapterMackeyGeneralBase.mackeyMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:52:44.717004+00:00
-- url     : https://prove2.me/submissions/aecd380a-ae27-4050-84a1-a0a12aa390e8

-- ID: 6a310cec-7f52-451c-9cdd-08d184ca1870 | NAME: BookProof.ChapterMackeyGeneralBase.mackeyMap_eq | 未本地编译验证
-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.mackeyMap_eq
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
open BookProof.ChapterMackeyGeneralBase

theorem solution (hs : ∀ x, s x • x₀ = x) (ψ : E) (x : X) :
    mackeyMap S s ψ x = S.p x₀ (S.U (s x)⁻¹ ψ) := by
  change S.U (s x)⁻¹ (S.p x ψ) = S.p x₀ (S.U (s x)⁻¹ ψ)
  have hact : (s x)⁻¹ • x = x₀ := by
    calc
      (s x)⁻¹ • x = (s x)⁻¹ • (s x • x₀) := by rw [hs x]
      _ = ((s x)⁻¹ * s x) • x₀ := by rw [mul_smul]
      _ = x₀ := by simp
  simpa [hact] using S.covariant (s x)⁻¹ x ψ
