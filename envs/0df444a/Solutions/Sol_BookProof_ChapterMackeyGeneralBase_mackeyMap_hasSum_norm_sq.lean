-- Prove2me | solution 1 for BookProof.ChapterMackeyGeneralBase.mackeyMap_hasSum_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:48:06.025875+00:00
-- url     : https://prove2.me/submissions/4ea72747-56fc-4e08-b00d-b59c99f7c49c

import Definitions.Def_ChapterOrthogonalSums
import Mathlib
import Definitions.Def_ChapterMackeyGeneralBase
import Definitions.Def_ChapterMackeyImprimitivity
import Theorems.Thm_BookProof_ChapterOrthogonalSums_hasSum_norm_sq_of_hasSum

open BookProof.ChapterMackeyImprimitivity
open scoped InnerProductSpace
open BookProof.ChapterOrthogonalSums
open BookProof.ChapterMackeyGeneralBase

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (S : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem G X E)
variable (S : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem G X E) (x₀ : X) (s : X → G)
variable {S x₀ s}

theorem solution (ψ : E) :
    HasSum (fun x => ‖mackeyMap S s ψ x‖ ^ 2) (‖ψ‖ ^ 2) := by
  have horth : ∀ x y, x ≠ y → ⟪S.p x ψ, S.p y ψ⟫_ℂ = 0 := by
    intro x y hxy
    rw [S.selfAdjoint x ψ (S.p y ψ), S.orthogonal x y hxy ψ]
    simp
  have hparseval := hasSum_norm_sq_of_hasSum (S.complete ψ) horth
  simpa [BookProof.ChapterMackeyGeneralBase.mackeyMap] using hparseval
