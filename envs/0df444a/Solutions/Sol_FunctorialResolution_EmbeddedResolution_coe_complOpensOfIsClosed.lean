-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.coe_complOpensOfIsClosed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:38.919038+00:00
-- url     : https://prove2.me/submissions/12f1c860-04d7-42ae-948e-012c22dec099

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ClopenSubscheme

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme} (C : X.Opens) (hC : IsClosed (C : Set X)) :
    ((complOpensOfIsClosed C hC : X.Opens) : Set X) = (C : Set X)ᶜ := rfl
end FunctorialResolution.EmbeddedResolution
