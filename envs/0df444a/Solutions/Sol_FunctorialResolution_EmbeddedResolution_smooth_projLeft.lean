-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.smooth_projLeft
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:50.369041+00:00
-- url     : https://prove2.me/submissions/df1dc44c-9530-4b3b-a369-c4c53eac0023

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
theorem _root_.solution (hs : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] (n m : ℕ) :
    AlgebraicGeometry.Smooth (projLeft k n m) := by
  have hsm : AlgebraicGeometry.Smooth (affineSpaceIndexedByToSpec k (ULift.{u} (Fin m))) := hs k m
  have hpb : IsPullback (projLeft k n m) (projRight k n m)
      (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)))
      (affineSpaceIndexedByToSpec k (ULift.{u} (Fin m))) :=
    isPullback_reindex_of_sumEquiv (sumUliftEquivUliftSum.{u} n m) (Spec (CommRingCat.of k))
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hsm
end FunctorialResolution.EmbeddedResolution
