-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.smooth_prodMapOnPreimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:30:29.039777+00:00
-- url     : https://prove2.me/submissions/ab3021a6-2830-4f45-8d1b-02769b742741

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceProduct
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isPullback_prodMapOnPreimage

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
theorem _root_.solution (_hs : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] (n m c : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens)
    (φ : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c)))
    [AlgebraicGeometry.Smooth φ]
    (hφ : φ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) =
      U.ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n))) :
    AlgebraicGeometry.Smooth (prodMapOnPreimage k n m c U φ) := by
  have hsmooth : AlgebraicGeometry.Smooth φ := ‹AlgebraicGeometry.Smooth φ›
  exact MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Smooth)
    (isPullback_prodMapOnPreimage k n m c U φ hφ).flip hsmooth
end FunctorialResolution.EmbeddedResolution
