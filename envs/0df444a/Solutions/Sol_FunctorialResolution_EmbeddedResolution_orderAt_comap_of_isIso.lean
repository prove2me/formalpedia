-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:23:36.812237+00:00
-- url     : https://prove2.me/submissions/bdaae398-ddd8-44d3-853e-3f0373c272a9

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_comap_of_isOpenImmersion

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
open CategoryTheory
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f] (J : B.IdealSheafData)
    (x : ↥A) : orderAt (J.comap f) x = orderAt J (f.base x) :=
  orderAt_comap_of_isOpenImmersion f J x
end FunctorialResolution.EmbeddedResolution
