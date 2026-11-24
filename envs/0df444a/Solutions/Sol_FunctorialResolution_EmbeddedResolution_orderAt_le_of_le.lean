-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAt_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:49.212882+00:00
-- url     : https://prove2.me/submissions/eea1fdeb-1deb-47e3-bf9b-6ea1fa527e90

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_mono
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_le_of_le


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
theorem _root_.solution {I J : X.IdealSheafData} (h : I ≤ J) (x : X) :
    orderAt J x ≤ orderAt I x :=
  idealOrder_le_of_le (stalkIdeal_mono h x)
end FunctorialResolution.EmbeddedResolution
