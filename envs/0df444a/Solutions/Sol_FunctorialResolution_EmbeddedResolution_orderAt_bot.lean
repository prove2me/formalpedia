-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAt_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:23:31.794266+00:00
-- url     : https://prove2.me/submissions/2a12923f-1443-4033-a5a1-3e6fdfa8a0be

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_bot
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_idealOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_bot


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
theorem _root_.solution (x : X) : orderAt (⊥ : X.IdealSheafData) x = ⊤ := by
  rw [orderAt_eq_idealOrder, stalkIdeal_bot, idealOrder_bot]
end FunctorialResolution.EmbeddedResolution
