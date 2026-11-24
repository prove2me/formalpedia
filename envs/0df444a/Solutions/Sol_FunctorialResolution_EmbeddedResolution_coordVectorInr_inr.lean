-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:17.737198+00:00
-- url     : https://prove2.me/submissions/5e1ffbd5-b285-4f69-a0e8-226cc11fc0d5

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates

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
theorem _root_.solution {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m))) (b : Fin m) :
    coordVectorInr n m f (ULift.up (Sum.inr b)) = pullbackCoord f (ULift.up b) := rfl
end FunctorialResolution.EmbeddedResolution
