-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAt_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:02:39.438801+00:00
-- url     : https://prove2.me/submissions/dbf73fa8-265a-4838-b9eb-1640f7c1ca5b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_sup
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_idealOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_sup


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
    orderAt (I ⊔ J) x = min (orderAt I x) (orderAt J x) := by
  rw [orderAt_eq_idealOrder, stalkIdeal_sup, idealOrder_sup]
  rfl
end FunctorialResolution.EmbeddedResolution
