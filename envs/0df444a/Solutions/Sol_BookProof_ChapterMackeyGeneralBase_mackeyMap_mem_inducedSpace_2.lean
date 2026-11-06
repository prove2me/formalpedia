-- Prove2me | solution 2 for BookProof.ChapterMackeyGeneralBase.mackeyMap_mem_inducedSpace
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:48:53.453764+00:00
-- url     : https://prove2.me/submissions/dbcede1b-329c-44ba-91cf-03ed0c76f89e

import Definitions.Def_ChapterMackeyGeneralBase
import Theorems.Thm_BookProof_ChapterOrthogonalSums_hasSum_norm_sq_of_hasSum

open BookProof.ChapterMackeyImprimitivity
open scoped InnerProductSpace
open BookProof.ChapterOrthogonalSums

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (S : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem G X E)
variable (S : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem G X E) (x₀ : X) (s : X → G)
variable {S x₀ s}

theorem solution (hs : ∀ x, s x • x₀ = x) (ψ : E) :
    BookProof.ChapterMackeyGeneralBase.mackeyMap S s ψ ∈
      BookProof.ChapterMackeyGeneralBase.InducedSpace S x₀ := by
  constructor
  · intro x
    have hx : (s x)⁻¹ • x = x₀ := by
      calc
        (s x)⁻¹ • x = (s x)⁻¹ • (s x • x₀) := by rw [hs x]
        _ = x₀ := inv_smul_smul _ _
    change S.p x₀ (S.U (s x)⁻¹ (S.p x ψ)) = S.U (s x)⁻¹ (S.p x ψ)
    rw [S.covariant, hx]
    exact S.idem x₀ _
  · have horth : ∀ x y, x ≠ y → ⟪S.p x ψ, S.p y ψ⟫_ℂ = 0 := by
      intro x y hxy
      rw [S.selfAdjoint, S.orthogonal x y hxy, inner_zero_right]
    have hsum := hasSum_norm_sq_of_hasSum (S.complete ψ) horth
    simpa only [BookProof.ChapterMackeyGeneralBase.mackeyMap,
      LinearIsometryEquiv.norm_map] using hsum.summable
