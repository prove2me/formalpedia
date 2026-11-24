-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mem_orderAtLeastLocus_iff_stalkIdeal_le_maximalIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:50:11.25791+00:00
-- url     : https://prove2.me/submissions/e8b30baa-b49c-469d-a640-1c31fcbf51c3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_orderAt_iff
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
theorem _root_.solution (I : X.IdealSheafData) (m : ℕ)
    (x : X) :
    x ∈ orderAtLeastLocus I m ↔
      stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ m := by
  rw [mem_orderAtLeastLocus_iff, le_orderAt_iff]
end FunctorialResolution.EmbeddedResolution
