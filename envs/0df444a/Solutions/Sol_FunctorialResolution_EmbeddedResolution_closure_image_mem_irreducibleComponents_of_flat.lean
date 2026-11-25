-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.closure_image_mem_irreducibleComponents_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:22:25.756589+00:00
-- url     : https://prove2.me/submissions/c01cd036-6637-4dc1-a60e-e5eb20c672b4

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SupportFlatPullback
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_closure_image_mem_irreducibleComponents_of_generalizingMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem generalizingMap_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Flat f] :
    GeneralizingMap (fun x : ↥X => f x) :=
  AlgebraicGeometry.Flat.generalizingMap f
namespace NonzeroOnComponents
end NonzeroOnComponents
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Flat f]
    {C : Set ↥X} (hC : C ∈ irreducibleComponents ↥X) :
    closure ((fun x : ↥X => f x) '' C) ∈ irreducibleComponents ↥Y :=
  closure_image_mem_irreducibleComponents_of_generalizingMap f (generalizingMap_of_flat f) hC
end FunctorialResolution.EmbeddedResolution
