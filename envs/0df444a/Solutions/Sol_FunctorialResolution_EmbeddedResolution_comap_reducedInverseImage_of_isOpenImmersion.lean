-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.comap_reducedInverseImage_of_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:04:05.931203+00:00
-- url     : https://prove2.me/submissions/d7cc2b33-1080-45b0-afac-823795eba452

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsOpenImmersion
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_reducedInverseImage_eq_vanishingIdeal_closedPreimage
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_comap_vanishingIdeal_of_isOpenImmersion
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_reducedInverseImage_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {A B Z : Scheme.{u}} (h : A ⟶ B)
    [IsOpenImmersion h] (f : B ⟶ Z) (W : TopologicalSpace.Closeds Z) :
    (reducedInverseImage f W).comap h = reducedInverseImage (h ≫ f) W := by
  rw [reducedInverseImage_eq_vanishingIdeal_closedPreimage, comap_vanishingIdeal_of_isOpenImmersion,
    reducedInverseImage_comp]
end FunctorialResolution.EmbeddedResolution
