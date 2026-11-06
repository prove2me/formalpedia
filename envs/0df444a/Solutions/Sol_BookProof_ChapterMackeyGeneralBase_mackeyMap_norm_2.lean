-- Prove2me | solution 2 for BookProof.ChapterMackeyGeneralBase.mackeyMap_norm
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:21:40.332901+00:00
-- url     : https://prove2.me/submissions/42287a64-f087-47d8-8bbd-5a5663928d6e

import Definitions.Def_ChapterOrthogonalSums
import Definitions.Def_ChapterMackeyGeneralBase
import Definitions.Def_ChapterMackeyImprimitivity

open BookProof.ChapterMackeyImprimitivity
open scoped InnerProductSpace
open BookProof.ChapterOrthogonalSums

variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (S : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem G X E)
variable (S : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem G X E) (x₀ : X) (s : X → G)
variable {S x₀ s}

theorem solution (ψ : E) (x : X) :
    ‖BookProof.ChapterMackeyGeneralBase.mackeyMap S s ψ x‖ = ‖S.p x ψ‖ := by
  simp [BookProof.ChapterMackeyGeneralBase.mackeyMap]
