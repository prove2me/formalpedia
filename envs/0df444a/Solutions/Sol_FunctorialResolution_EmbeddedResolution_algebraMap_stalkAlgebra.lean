-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.algebraMap_stalkAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:17:32.758276+00:00
-- url     : https://prove2.me/submissions/a226de26-72bb-4da1-81d2-cef7b791cbae

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease

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
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    @algebraMap k (X.presheaf.stalk x) _ _ (stalkAlgebra k p x) = stalkAlgebraMap k p x :=
  rfl
end FunctorialResolution.EmbeddedResolution
