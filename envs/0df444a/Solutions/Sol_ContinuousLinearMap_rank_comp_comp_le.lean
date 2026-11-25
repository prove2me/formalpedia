-- Prove2me | solution 1 for ContinuousLinearMap.rank_comp_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:52:55.261088+00:00
-- url     : https://prove2.me/submissions/545b5046-3a0b-410a-ab5b-77f7ae2254ab

module
public import Definitions.Def_SNumbers_Basic
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Theorems.Thm_ContinuousLinearMap_rank_zero
attribute [local simp] ContinuousLinearMap.rank_zero

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace ContinuousLinearMap
theorem _root_.solution (A : W →L[𝕜] X) (L : X →L[𝕜] Y) (B : Y →L[𝕜] Z) :
    (B.comp (L.comp A)).rank ≤ L.rank := by
  have hsub :
      LinearMap.range (B.comp (L.comp A) : W →ₗ[𝕜] Z) ≤
        Submodule.map (B : Y →ₗ[𝕜] Z) (LinearMap.range (L : X →ₗ[𝕜] Y)) := by
    intro z hz
    obtain ⟨w, hw⟩ := hz
    exact ⟨L (A w), ⟨A w, rfl⟩, by simpa using hw⟩
  calc Module.rank 𝕜 (LinearMap.range (B.comp (L.comp A) : W →ₗ[𝕜] Z))
      ≤ Module.rank 𝕜
          (Submodule.map (B : Y →ₗ[𝕜] Z) (LinearMap.range (L : X →ₗ[𝕜] Y))) :=
        Submodule.rank_mono hsub
    _ ≤ Module.rank 𝕜 (LinearMap.range (L : X →ₗ[𝕜] Y)) :=
        rank_map_le _ _
end ContinuousLinearMap
