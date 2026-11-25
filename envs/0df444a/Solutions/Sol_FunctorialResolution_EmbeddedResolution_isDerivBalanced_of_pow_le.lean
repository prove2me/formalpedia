-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isDerivBalanced_of_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:21:57.892804+00:00
-- url     : https://prove2.me/submissions/2e553907-8011-4880-8e59-860824dd61d2

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
theorem _root_.solution {I : X.IdealSheafData} {m : ℕ}
    (h : ∀ i < m, derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i)) : IsDerivBalanced k p I m :=
  h
end FunctorialResolution.EmbeddedResolution
