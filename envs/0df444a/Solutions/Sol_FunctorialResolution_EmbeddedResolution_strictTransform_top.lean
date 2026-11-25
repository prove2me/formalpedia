-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.strictTransform_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:25:23.013969+00:00
-- url     : https://prove2.me/submissions/d1b50c60-14a1-49da-8a93-3679d0e29f0d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupIsoOffCenter
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_OpenImmersionAppLE
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ReducedSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_comap_le_strictTransform
import Theorems.Thm_FunctorialResolution_Blowup_comap_le_strictTransform


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
theorem _root_.solution {X' X : Scheme.{u}} (f : X' ⟶ X) (Z : X.IdealSheafData) :
    Blowup.strictTransform f Z (⊤ : X.IdealSheafData) = ⊤ := by
  have h := comap_le_strictTransform f Z ⊤
  rw [Scheme.IdealSheafData.comap_top] at h
  exact le_antisymm le_top h
end FunctorialResolution.EmbeddedResolution
