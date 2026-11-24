-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.coe_complSUnionOtherComponents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:47:42.269979+00:00
-- url     : https://prove2.me/submissions/f5e39b63-42ad-4783-a357-d2ce8171984d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_KernelFlatBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_VanishingIdealOfComponents

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
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {α : Type*} [TopologicalSpace α]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (X : Scheme.{u}) [NoetherianSpace ↥X] (S : Set (Set ↥X)) :
    (complSUnionOtherComponents X S : Set ↥X) = (⋃₀ (irreducibleComponents ↥X \ S))ᶜ :=
  rfl
end FunctorialResolution.EmbeddedResolution
