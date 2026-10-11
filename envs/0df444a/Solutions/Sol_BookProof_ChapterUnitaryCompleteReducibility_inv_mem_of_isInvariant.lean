-- Prove2me | solution 1 for BookProof.ChapterUnitaryCompleteReducibility.inv_mem_of_isInvariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:15:07.206947+00:00
-- url     : https://prove2.me/submissions/9a082ab1-d1b4-4f7d-be0d-c98492f4383e

-- Generated from ChapterUnitaryCompleteReducibility.lean — solution of BookProof.ChapterUnitaryCompleteReducibility.inv_mem_of_isInvariant
import Mathlib
import Definitions.Def_ChapterUnitaryCompleteReducibility
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterUnitaryCompleteReducibility




open Submodule

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

set_option maxHeartbeats 1000000 in
theorem solution {ρ : G →* (V ≃ₗᵢ[ℂ] V)} {W : Submodule ℂ V}
    (hW : IsInvariant ρ W) (g : G) {x : V} (hx : x ∈ W) : (ρ g).symm x ∈ W := by

  have h : ρ g⁻¹ x ∈ W := hW g⁻¹ x hx
  have hsymm : (ρ g).symm x = ρ g⁻¹ x := by simp [map_inv]
  rwa [hsymm]
