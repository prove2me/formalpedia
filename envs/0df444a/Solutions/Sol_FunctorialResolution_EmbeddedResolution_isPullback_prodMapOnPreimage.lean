-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isPullback_prodMapOnPreimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:05:31.635965+00:00
-- url     : https://prove2.me/submissions/14079b61-e881-481a-8ead-6ba514b58d60

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceProduct
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isPullback_projLeft_projRight
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_prodMapOnPreimage_comp_projRight
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_morphismRestrict_projLeft_comp

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
theorem _root_.solution (k : Type u) [Field k] (n m c : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens)
    (φ : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c)))
    (hφ : φ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) =
      U.ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n))) :
    IsPullback (prodMapOnPreimage k n m c U φ)
      (AlgebraicGeometry.morphismRestrict (projLeft k n m) U)
      (projLeft k c m) φ := by
  have hsq1 : IsPullback (AlgebraicGeometry.morphismRestrict (projLeft k n m) U)
      (projLeft k n m ⁻¹ᵁ U).ι U.ι (projLeft k n m) :=
    AlgebraicGeometry.isPullback_morphismRestrict (projLeft k n m) U
  have hstar := hsq1.paste_vert (isPullback_projLeft_projRight k n m)
  have hstar' : IsPullback (AlgebraicGeometry.morphismRestrict (projLeft k n m) U)
      (prodMapOnPreimage k n m c U φ ≫ projRight k c m)
      (φ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)))
      (affineSpaceIndexedByToSpec k (ULift.{u} (Fin m))) := by
    rw [prodMapOnPreimage_comp_projRight, hφ]
    exact hstar
  exact (hstar'.of_bot (morphismRestrict_projLeft_comp k n m c U φ hφ)
    (isPullback_projLeft_projRight k c m)).flip
end FunctorialResolution.EmbeddedResolution
