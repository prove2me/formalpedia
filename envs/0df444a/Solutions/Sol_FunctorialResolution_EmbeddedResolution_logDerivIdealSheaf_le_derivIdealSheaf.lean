-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.logDerivIdealSheaf_le_derivIdealSheaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:22:34.448597+00:00
-- url     : https://prove2.me/submissions/b77d0488-181e-4596-958c-1ca19a1cf27e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealSheaf
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdeal_le_derivIdeal


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
    logDerivIdealSheaf k p P I ≤ derivIdealSheaf k p I := by
  intro U
  exact @logDerivIdeal_le_derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) (I.ideal U)
end FunctorialResolution.EmbeddedResolution
