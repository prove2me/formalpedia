-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAt_eq_of_stalkIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:23:42.021383+00:00
-- url     : https://prove2.me/submissions/50a5e22a-9ecd-4d66-909f-4e4bad0ae927

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_idealOrder

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
theorem _root_.solution {I J : X.IdealSheafData} {x : X}
    (h : stalkIdeal I x = stalkIdeal J x) : orderAt I x = orderAt J x := by
  rw [orderAt_eq_idealOrder, orderAt_eq_idealOrder, h]
end FunctorialResolution.EmbeddedResolution
