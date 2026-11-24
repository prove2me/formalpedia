-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.imageIdealSheaf_comap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:24.098438+00:00
-- url     : https://prove2.me/submissions/368fee08-0b23-4829-bddf-c91286c4c569

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_IsomorphismTransport
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_imageIdealSheaf_eq_comap_inv

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
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f]
    (I : B.IdealSheafData) :
    imageIdealSheaf f (I.comap f) = I := by
  rw [imageIdealSheaf_eq_comap_inv, ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
    IsIso.inv_hom_id, AlgebraicGeometry.Scheme.IdealSheafData.comap_id]
end FunctorialResolution.EmbeddedResolution
