-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.strictTransform_eq_ker_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:51:27.514832+00:00
-- url     : https://prove2.me/submissions/381e428b-b072-40f8-bf9c-d8ae46821b8f

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
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_strictTransform__eq___comp_subscheme__ababdba2b9f4
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_strictTransform_eq_ker_strictTransform__ddf54f1c1d60
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_ker___preimage_comp_subscheme__eq_ker_comap_1c8ee5f81d10

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
theorem _root_.solution {X X₁ : Scheme.{u}} (f : X₁ ⟶ X)
    (W D₁ : X.IdealSheafData) :
    Blowup.strictTransform f W D₁ =
      (((D₁.comap (Scheme.Opens.ι W.support.compl)).comap
            (f ∣_ W.support.compl)).subschemeι ≫
          Scheme.Opens.ι (f ⁻¹ᵁ W.support.compl)).ker := by
  have hUV : (W.comap f).support.compl = f ⁻¹ᵁ W.support.compl := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hcomap : (D₁.comap f).comap (Scheme.Opens.ι (f ⁻¹ᵁ W.support.compl))
      = (D₁.comap (Scheme.Opens.ι W.support.compl)).comap (f ∣_ W.support.compl) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  rw [strictTransform_eq_ker_strictTransformι, strictTransformι_eq_ι_comp_subschemeι]
  show (Scheme.Opens.ι ((D₁.comap f).subschemeι ⁻¹ᵁ (W.comap f).support.compl) ≫
      (D₁.comap f).subschemeι).ker = _
  rw [hUV, ker_ι_preimage_comp_subschemeι_eq_ker_comap, hcomap]
end FunctorialResolution.EmbeddedResolution
