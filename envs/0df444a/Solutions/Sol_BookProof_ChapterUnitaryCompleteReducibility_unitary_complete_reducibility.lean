-- Prove2me | solution 1 for BookProof.ChapterUnitaryCompleteReducibility.unitary_complete_reducibility
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:16:02.362749+00:00
-- url     : https://prove2.me/submissions/6750d0ec-c899-4c34-8ccb-b0ca5c7940bf

-- Generated from ChapterUnitaryCompleteReducibility.lean — solution of BookProof.ChapterUnitaryCompleteReducibility.unitary_complete_reducibility
import Mathlib
import Definitions.Def_ChapterUnitaryCompleteReducibility
import Theorems.Thm_BookProof_ChapterUnitaryCompleteReducibility_orthogonal_isInvariant
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterUnitaryCompleteReducibility




open Submodule

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

set_option maxHeartbeats 1000000 in
theorem solution [FiniteDimensional ℂ V]
    {ρ : G →* (V ≃ₗᵢ[ℂ] V)} {W : Submodule ℂ V} (hW : IsInvariant ρ W) :
    ∃ W' : Submodule ℂ V, IsInvariant ρ W' ∧ IsCompl W W' := ⟨Wᗮ, orthogonal_isInvariant hW, Submodule.isCompl_orthogonal_of_hasOrthogonalProjection⟩
