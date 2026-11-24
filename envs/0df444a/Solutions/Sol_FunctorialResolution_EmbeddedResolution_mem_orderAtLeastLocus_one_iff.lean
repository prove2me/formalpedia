-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mem_orderAtLeastLocus_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:25.587809+00:00
-- url     : https://prove2.me/submissions/5c7f410e-e158-4e57-b527-46dd3582c3ad

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_one_le_orderAt_iff_mem_support
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_orderAtLeastLocus_iff

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
    x ∈ orderAtLeastLocus I 1 ↔ x ∈ I.support := by
  rw [mem_orderAtLeastLocus_iff, Nat.cast_one, one_le_orderAt_iff_mem_support]
end FunctorialResolution.EmbeddedResolution
