-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.logDerivIdealSheafIterate_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:24:14.579284+00:00
-- url     : https://prove2.me/submissions/f343dc6b-0261-4a62-b471-4529f337cfc1

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealSheaf

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
theorem _root_.solution (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P I : X.IdealSheafData) :
    logDerivIdealSheafIterate k p P 1 I = logDerivIdealSheaf k p P I :=
  rfl
end FunctorialResolution.EmbeddedResolution
