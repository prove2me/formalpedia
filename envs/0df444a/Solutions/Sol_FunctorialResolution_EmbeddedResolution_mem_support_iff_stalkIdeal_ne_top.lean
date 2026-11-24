-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mem_support_iff_stalkIdeal_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:44.572805+00:00
-- url     : https://prove2.me/submissions/34afe957-3ea3-417d-bf04-3e120fe7d8b7

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_support_iff_stalkIdeal_le_maximalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (I : X.IdealSheafData) (x : X) :
    x ∈ I.support ↔ stalkIdeal I x ≠ ⊤ := by
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal]
  refine ⟨fun h htop => ?_, fun h => IsLocalRing.le_maximalIdeal h⟩
  rw [htop, top_le_iff] at h
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top h
end FunctorialResolution.EmbeddedResolution
