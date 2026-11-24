-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.isLocallyNoetherian_subscheme_of_isSmoothDivisor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:38:39.63175+00:00
-- url     : https://prove2.me/submissions/4e3b991a-df7c-4b74-81c8-0e13a30d314b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_VanishingIdealAssignment
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_VanishingIdealOrderOne

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
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
theorem _root_.solution
    (k : Type u) [Field k] (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k))
    (U : W.Opens) (D : (U.toScheme).IdealSheafData)
    (hD : IsSmoothDivisor (U.ι ≫ p) D) :
    IsLocallyNoetherian D.subscheme := by
  obtain ⟨_, hsm⟩ := hD
  have : AlgebraicGeometry.Smooth (D.subschemeι ≫ U.ι ≫ p) := hsm
  have : LocallyOfFiniteType (D.subschemeι ≫ U.ι ≫ p) := inferInstance
  have : IsNoetherianRing (CommRingCat.of k) := inferInstanceAs (IsNoetherianRing k)
  exact AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian (D.subschemeι ≫ U.ι ≫ p)
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
