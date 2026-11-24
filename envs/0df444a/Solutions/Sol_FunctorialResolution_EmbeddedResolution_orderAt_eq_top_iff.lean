-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAt_eq_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:50:13.634943+00:00
-- url     : https://prove2.me/submissions/0b730c8f-3a19-4b3f-b749-91d309775327

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_idealOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_ne_top_of_stalkIdeal_ne_bot
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
theorem _root_.solution [IsLocallyNoetherian X] (I : X.IdealSheafData) (x : X) :
    orderAt I x = ⊤ ↔ stalkIdeal I x = ⊥ := by
  constructor
  · intro h
    by_contra hne
    exact orderAt_ne_top_of_stalkIdeal_ne_bot I x hne h
  · intro h
    rw [orderAt_eq_idealOrder, h, idealOrder_bot]
end FunctorialResolution.EmbeddedResolution
