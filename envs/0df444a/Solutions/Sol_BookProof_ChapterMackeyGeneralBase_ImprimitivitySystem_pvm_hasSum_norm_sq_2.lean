-- Prove2me | solution 2 for BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.pvm_hasSum_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:47:00.739452+00:00
-- url     : https://prove2.me/submissions/788164f9-6b7e-4385-ab3e-3b79c3fd4fa5

import Definitions.Def_ChapterOrthogonalSums
import Definitions.Def_ChapterMackeyGeneralBase
import Definitions.Def_ChapterMackeyImprimitivity
import Theorems.Thm_BookProof_ChapterOrthogonalSums_hasSum_norm_sq_of_hasSum

open BookProof.ChapterMackeyImprimitivity
open scoped InnerProductSpace
open BookProof.ChapterOrthogonalSums

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (S : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem G X E)

theorem solution (ψ : E) : HasSum (fun x => ‖S.p x ψ‖ ^ 2) (‖ψ‖ ^ 2) := by
  apply BookProof.ChapterOrthogonalSums.hasSum_norm_sq_of_hasSum (S.complete ψ)
  intro x y hxy
  calc
    ⟪S.p x ψ, S.p y ψ⟫_ℂ = ⟪ψ, S.p x (S.p y ψ)⟫_ℂ := S.selfAdjoint x ψ (S.p y ψ)
    _ = 0 := by rw [S.orthogonal x y hxy, inner_zero_right]
