-- Prove2me | solution 1 for BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.inner_pvm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:49:34.787201+00:00
-- url     : https://prove2.me/submissions/02b7048b-8539-475b-bc76-a1f9b3ef93f2

import Definitions.Def_ChapterMackeyGeneralBase

open BookProof.ChapterMackeyGeneralBase
open scoped InnerProductSpace

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (S : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem G X E)

theorem solution {x y : X} (hxy : x ≠ y) (ψ φ : E) :
    ⟪S.p x ψ, S.p y φ⟫_ℂ = 0 := by
  rw [S.selfAdjoint x ψ (S.p y φ), S.orthogonal x y hxy, inner_zero_right]
