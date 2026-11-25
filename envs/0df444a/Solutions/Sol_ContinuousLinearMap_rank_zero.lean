-- Prove2me | solution 1 for ContinuousLinearMap.rank_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:34:51.408653+00:00
-- url     : https://prove2.me/submissions/a4eae69d-050c-4556-94f4-7068a63e2644

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
theorem _root_.solution : (0 : X →L[𝕜] Y).rank = 0 := by simp
end ContinuousLinearMap
