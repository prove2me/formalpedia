-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_of_isOpenImmersion_of_coe_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:22:41.495471+00:00
-- url     : https://prove2.me/submissions/cfb12d5c-2184-4f56-9a17-27b86c13168f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsOpenImmersion
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_closedPreimage_coe
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_comap_vanishingIdeal_of_isOpenImmersion

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
theorem _root_.solution {X' Y' : Scheme.{u}} (h : X' ⟶ Y')
    [IsOpenImmersion h] (Z : TopologicalSpace.Closeds Y') (Z' : TopologicalSpace.Closeds X')
    (hZ' : (Z' : Set X') = h.base ⁻¹' (Z : Set Y')) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap h
      = Scheme.IdealSheafData.vanishingIdeal Z' := by
  have h1 : closedPreimage h Z = Z' := SetLike.ext' (by rw [closedPreimage_coe, hZ'])
  rw [comap_vanishingIdeal_of_isOpenImmersion, h1]
end FunctorialResolution.EmbeddedResolution
