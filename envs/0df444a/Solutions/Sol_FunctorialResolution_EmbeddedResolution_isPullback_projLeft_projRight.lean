-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isPullback_projLeft_projRight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:26:32.840895+00:00
-- url     : https://prove2.me/submissions/1e3982a4-e93d-4008-864e-e2238757f76d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceProduct
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isPullback_reindex_of_sumEquiv

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
theorem _root_.solution (k : Type u) [Field k] (n m : ℕ) :
    IsPullback (projLeft k n m) (projRight k n m)
      (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)))
      (affineSpaceIndexedByToSpec k (ULift.{u} (Fin m))) :=
  isPullback_reindex_of_sumEquiv (sumUliftEquivUliftSum.{u} n m) (Spec (CommRingCat.of k))
end FunctorialResolution.EmbeddedResolution
