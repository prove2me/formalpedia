-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_def
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:36.821903+00:00
-- url     : https://prove2.me/submissions/1b8743a2-26b9-4616-8b21-2ebee827e8bd

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
variable [Algebra (MvPolynomial ι k) S]
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution (i : ι) :
    coord k ι S i = algebraMap (MvPolynomial ι k) S (MvPolynomial.X i) := rfl
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
