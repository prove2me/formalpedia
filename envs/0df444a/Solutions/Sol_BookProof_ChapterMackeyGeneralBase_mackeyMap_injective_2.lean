-- Prove2me | solution 2 for BookProof.ChapterMackeyGeneralBase.mackeyMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:57:06.167502+00:00
-- url     : https://prove2.me/submissions/b12cd5de-5c95-45ac-8ba4-156717911413

-- ID: f76317be-255b-4a95-b116-a977e59fa595 | NAME: BookProof.ChapterMackeyGeneralBase.mackeyMap_injective | 未本地编译验证
-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.mackeyMap_injective
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

theorem solution : Function.Injective (BookProof.ChapterMackeyGeneralBase.mackeyMap S s) := by
  intro ψ φ hEq
  have hp : ∀ x : X, S.p x ψ = S.p x φ := by
    intro x
    have hx : S.U (s x)⁻¹ (S.p x ψ) = S.U (s x)⁻¹ (S.p x φ) := by
      simpa [BookProof.ChapterMackeyGeneralBase.mackeyMap] using congrFun hEq x
    exact (S.U (s x)⁻¹).injective hx
  have hf : (fun x : X => S.p x ψ) = (fun x : X => S.p x φ) :=
    funext (fun x => hp x)
  have hφ : HasSum (fun x : X => S.p x ψ) φ := by
    simpa only [hf] using (S.complete φ)
  exact (S.complete ψ).unique hφ
