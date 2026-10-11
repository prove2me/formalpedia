-- Prove2me | solution 1 for BookProof.ChapterUnitaryCompleteReducibility.orthogonal_isInvariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:15:21.358966+00:00
-- url     : https://prove2.me/submissions/3470ff4f-bd7c-4b64-ba1e-35cf81ad11ae

-- Generated from ChapterUnitaryCompleteReducibility.lean — solution of BookProof.ChapterUnitaryCompleteReducibility.orthogonal_isInvariant
import Mathlib
import Definitions.Def_ChapterUnitaryCompleteReducibility
import Theorems.Thm_BookProof_ChapterUnitaryCompleteReducibility_inv_mem_of_isInvariant
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterUnitaryCompleteReducibility




open Submodule

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

set_option maxHeartbeats 1000000 in
theorem solution {ρ : G →* (V ≃ₗᵢ[ℂ] V)} {W : Submodule ℂ V}
    (hW : IsInvariant ρ W) : IsInvariant ρ Wᗮ := by

  intro g y hy
  rw [Submodule.mem_orthogonal]
  intro x hx
  have hx' : (ρ g).symm x ∈ W := inv_mem_of_isInvariant hW g hx
  have := hy ((ρ g).symm x) hx'
  calc inner ℂ x (ρ g y) = inner ℂ (ρ g ((ρ g).symm x)) (ρ g y) := by
        rw [LinearIsometryEquiv.apply_symm_apply]
    _ = inner ℂ ((ρ g).symm x) y := LinearIsometryEquiv.inner_map_map _ _ _
    _ = 0 := this
