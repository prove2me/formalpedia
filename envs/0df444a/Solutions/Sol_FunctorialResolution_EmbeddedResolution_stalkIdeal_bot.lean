-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.stalkIdeal_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:51:24.081716+00:00
-- url     : https://prove2.me/submissions/cb4e7208-9655-4323-b304-209da079c717

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder

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
theorem _root_.solution (x : X) : stalkIdeal (⊥ : X.IdealSheafData) x = ⊥ := by
  have h : ∀ U : X.affineOpens, (⊥ : X.IdealSheafData).ideal U = ⊥ := fun U => by simp
  simp only [stalkIdeal, h, Ideal.map_bot, iSup_bot]
end FunctorialResolution.EmbeddedResolution
