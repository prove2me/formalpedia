-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:36.0021+00:00
-- url     : https://prove2.me/submissions/e74b00a4-f7c2-4cf5-a94d-44c34425ab2a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_JacobianCriterion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_FormallyEtaleCoordinates
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_def


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S] (S' : Type*) [CommRing S']
  [Algebra (MvPolynomial ι k) S] [Algebra (MvPolynomial ι k) S'] [Algebra S S']
  [IsScalarTower (MvPolynomial ι k) S S']
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution (i : ι) :
    algebraMap S S' (coord k ι S i) = coord k ι S' i := by
  rw [coord_def, coord_def]
  exact (IsScalarTower.algebraMap_apply (MvPolynomial ι k) S S' (MvPolynomial.X i)).symm
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
