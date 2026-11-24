-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.add_orderAt_le_orderAt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:01:28.202328+00:00
-- url     : https://prove2.me/submissions/77b3a114-aeb1-4066-ba57-d6bb0a397132

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_mul
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_idealOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_add_idealOrder_le_idealOrder_mul


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
theorem _root_.solution (I J : X.IdealSheafData) (x : X) :
    orderAt I x + orderAt J x ≤ orderAt (I * J) x := by
  rw [orderAt_eq_idealOrder (I * J), stalkIdeal_mul]
  exact add_idealOrder_le_idealOrder_mul (stalkIdeal I x) (stalkIdeal J x)
end FunctorialResolution.EmbeddedResolution
