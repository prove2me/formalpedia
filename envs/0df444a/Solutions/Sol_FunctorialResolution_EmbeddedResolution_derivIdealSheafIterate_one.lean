-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:21:33.722775+00:00
-- url     : https://prove2.me/submissions/4b482a0b-7cc4-445c-86c2-8bd82416d2fd

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf

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
theorem _root_.solution (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData) :
    derivIdealSheafIterate k p 1 I = derivIdealSheaf k p I :=
  rfl
end FunctorialResolution.EmbeddedResolution
