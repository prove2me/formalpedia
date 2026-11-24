-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isScalarTower_stalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:57:02.331154+00:00
-- url     : https://prove2.me/submissions/18eb1110-a589-4a95-9763-6d82e7877f23

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_sectionsAlgebraMap_comp_germ

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
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (x : X) (hx : x ∈ U)
    [Algebra k Γ(X, U)] [Algebra k (X.presheaf.stalk x)] [Algebra Γ(X, U) (X.presheaf.stalk x)]
    (hU : algebraMap k Γ(X, U) = sectionsAlgebraMap k p U)
    (hstalk : algebraMap k (X.presheaf.stalk x) = stalkAlgebraMap k p x)
    (hgerm : algebraMap Γ(X, U) (X.presheaf.stalk x) = (X.presheaf.germ U x hx).hom) :
    IsScalarTower k Γ(X, U) (X.presheaf.stalk x) := by
  refine IsScalarTower.of_algebraMap_eq' ?_
  rw [hstalk, hgerm, hU, sectionsAlgebraMap_comp_germ]
end FunctorialResolution.EmbeddedResolution
