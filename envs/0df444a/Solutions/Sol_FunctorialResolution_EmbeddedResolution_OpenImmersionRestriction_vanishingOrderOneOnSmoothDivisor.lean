-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.vanishingOrderOneOnSmoothDivisor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:22:14.062368+00:00
-- url     : https://prove2.me/submissions/ffa3e29e-7e44-474e-8030-b524daf6563c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_VanishingIdealAssignment
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_VanishingIdealOrderOne
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_orderAt_vanishingIdeal_eq_one_of_not_mem_irreducibleComponents
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isLocallyNoetherian_subscheme_of_isSmoothDivisor
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_vanishingIdealAssignment_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
theorem _root_.solution : VanishingOrderOneOnSmoothDivisor.{u} := by
  intro k hk W p U D hD T y hy hT
  have : IsLocallyNoetherian D.subscheme :=
    isLocallyNoetherian_subscheme_of_isSmoothDivisor k W p U D hD
  rw [vanishingIdealAssignment_apply]
  exact orderAt_vanishingIdeal_eq_one_of_not_mem_irreducibleComponents D.subscheme T y hy hT
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
