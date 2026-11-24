-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:50:11.682016+00:00
-- url     : https://prove2.me/submissions/ea6cc080-3634-44f6-8d64-2068674fb30e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceGlobalSections

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
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (v : Type u)
    (s : Γ(affineSpaceIndexedBy k v, ⊤)) :
    (mvPolynomialEquivGlobalSections k v).symm s =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).hom
        ((affineSpaceIsoSpecMvPolynomial k v).inv.appTop s) := rfl
end FunctorialResolution.EmbeddedResolution
