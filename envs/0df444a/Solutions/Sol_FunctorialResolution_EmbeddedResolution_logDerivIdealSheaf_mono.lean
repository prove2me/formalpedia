-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.logDerivIdealSheaf_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:22:35.353693+00:00
-- url     : https://prove2.me/submissions/d929ca4e-eaaa-4823-b38e-0c887d6dc78b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealSheaf
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdeal_le_logDerivIdeal


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
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (P : X.IdealSheafData) :
    Monotone (logDerivIdealSheaf k p P) := by
  intro I J h U
  exact @logDerivIdeal_le_logDerivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U)
    (I.ideal U) (J.ideal U) (h U)
end FunctorialResolution.EmbeddedResolution
