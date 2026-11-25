-- Prove2me | solution 1 for ContinuousLinearMap.eq_zero_of_rank_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:26:37.832832+00:00
-- url     : https://prove2.me/submissions/7c2b9c98-7cb5-4be9-88ed-66e56d6c0264

module
public import Definitions.Def_SNumbers_Basic
public import Definitions.Def_SNumbers_ContinuousLinearMapRank

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace ContinuousLinearMap
theorem _root_.solution {L : X →L[𝕜] Y}
    (hL : L.rank ≤ (0 : Cardinal)) : L = 0 := by
  have hbot : LinearMap.range (L : X →ₗ[𝕜] Y) = ⊥ :=
    Submodule.rank_eq_zero.mp (le_antisymm hL zero_le)
  exact ContinuousLinearMap.coe_injective (LinearMap.range_eq_bot.mp hbot)
end ContinuousLinearMap
