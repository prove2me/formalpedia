-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.support_strictTransform_eq_closure_sdiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:24:18.48636+00:00
-- url     : https://prove2.me/submissions/4e224d49-1ef8-4249-9dcf-b7e0b0aa4f5a

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_support_strictTransform_eq_closure_preimage

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
theorem _root_.solution {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z D)] :
    ((Blowup.strictTransform π Z D).support : Set X₁) =
      closure (((D.comap π).support : Set X₁) \ ((Z.comap π).support : Set X₁)) := by
  have h1 : (((Z.comap π).support : Closeds X₁) : Set X₁) =
      ⇑π.base ⁻¹' (Z.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have h2 : (((D.comap π).support : Closeds X₁) : Set X₁) =
      ⇑π.base ⁻¹' (D.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  rw [support_strictTransform_eq_closure_preimage π Z D, h1, h2, Set.preimage_sdiff]
end FunctorialResolution.EmbeddedResolution
