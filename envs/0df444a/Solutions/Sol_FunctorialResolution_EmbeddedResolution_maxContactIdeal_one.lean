-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.maxContactIdeal_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:22:54.005086+00:00
-- url     : https://prove2.me/submissions/b3d6a951-dd6d-47eb-980b-3e971a2848b6

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (I : X.IdealSheafData) : maxContactIdeal k p I 1 = I :=
  rfl
end FunctorialResolution.EmbeddedResolution
