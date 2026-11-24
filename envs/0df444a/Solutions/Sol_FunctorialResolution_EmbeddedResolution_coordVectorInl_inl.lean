-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:54.629227+00:00
-- url     : https://prove2.me/submissions/49a433d2-1e7b-472f-9ab9-8204ad5be7f5

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
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n))) (a : Fin n) :
    coordVectorInl n m f (ULift.up (Sum.inl a)) = pullbackCoord f (ULift.up a) := rfl
end FunctorialResolution.EmbeddedResolution
