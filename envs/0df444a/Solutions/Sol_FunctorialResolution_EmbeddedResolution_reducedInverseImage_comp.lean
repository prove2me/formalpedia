-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.reducedInverseImage_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:50:06.535292+00:00
-- url     : https://prove2.me/submissions/fd320088-e162-4f7b-95f8-ed3ad721641d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsOpenImmersion
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_reducedInverseImage_eq_vanishingIdeal_closedPreimage

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
theorem _root_.solution {A B Z : Scheme.{u}} (g : A ⟶ B) (f : B ⟶ Z)
    (W : TopologicalSpace.Closeds Z) :
    reducedInverseImage (g ≫ f) W
      = Scheme.IdealSheafData.vanishingIdeal (closedPreimage g (closedPreimage f W)) := by
  have h : closedPreimage (g ≫ f) W = closedPreimage g (closedPreimage f W) := by
    apply SetLike.ext'
    show (g ≫ f).base ⁻¹' (W : Set Z) = g.base ⁻¹' (f.base ⁻¹' (W : Set Z))
    ext p
    simp
  rw [reducedInverseImage_eq_vanishingIdeal_closedPreimage, h]
end FunctorialResolution.EmbeddedResolution
