-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.ringKrullDim_stalk_le_topologicalKrullDim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:50:10.681427+00:00
-- url     : https://prove2.me/submissions/8139e9ef-f9f8-41d9-892d-f7b9670d307a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_AffineSpaceJacobson
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StalkKrullDimension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (X : Scheme.{u}) (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
  have hemb : Topology.IsEmbedding (X.fromSpecStalk x).base :=
    AlgebraicGeometry.Scheme.Hom.isEmbedding (X.fromSpecStalk x)
  have h1 : ringKrullDim (X.presheaf.stalk x) ≤
      topologicalKrullDim (PrimeSpectrum (X.presheaf.stalk x)) :=
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).ge
  have h2 : topologicalKrullDim ↥(Spec (X.presheaf.stalk x)) ≤ topologicalKrullDim ↥X :=
    hemb.toIsInducing.topologicalKrullDim_le
  exact le_trans h1 h2
end FunctorialResolution.EmbeddedResolution
