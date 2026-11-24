-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.support_strictTransform_eq_closure_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:03:39.217395+00:00
-- url     : https://prove2.me/submissions/437b2a84-0559-4788-8bf4-a719730e9c1e

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coe_strictTransformOpens
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_strictTransform__eq___comp_subscheme__ababdba2b9f4
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_strictTransform_eq_ker_strictTransform__ddf54f1c1d60
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem range_comp_eq_image_range {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Set.range ⇑(f ≫ g) = ⇑g '' Set.range ⇑f := by
  ext x
  simp [Set.range_comp]
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z D)] :
    ((Blowup.strictTransform π Z D).support : Set X₁) =
      closure (⇑π.base ⁻¹' ((D.support : Set X) \ (Z.support : Set X))) := by
  have h1 : (((Z.comap π).support.compl : X₁.Opens) : Set X₁) =
      (⇑π.base ⁻¹' (Z.support : Set X))ᶜ := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have h2 : (((D.comap π).support : Closeds X₁) : Set X₁) =
      ⇑π.base ⁻¹' (D.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  rw [strictTransform_eq_ker_strictTransformι, Scheme.Hom.support_ker]
  congr 1
  rw [strictTransformι_eq_ι_comp_subschemeι, range_comp_eq_image_range, Scheme.Opens.range_ι,
    coe_strictTransformOpens, Set.image_preimage_eq_inter_range,
    Scheme.IdealSheafData.range_subschemeι, h1, h2]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_preimage, Set.mem_sdiff]
  tauto
end FunctorialResolution.EmbeddedResolution
