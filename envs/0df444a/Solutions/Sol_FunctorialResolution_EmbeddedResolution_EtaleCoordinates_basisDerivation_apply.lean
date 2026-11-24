-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:17.642151+00:00
-- url     : https://prove2.me/submissions/cd497782-dc33-414a-84fc-24cd6fc273bd

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
variable [Algebra (MvPolynomial ι k) S] [Algebra k S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
include ι
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution [Fintype ι] [DecidableEq ι] (i : ι) :
    basisDerivation k ι S i = partialDeriv k ι S i :=
  (exists_basisDerivation k ι S).choose_spec i
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
