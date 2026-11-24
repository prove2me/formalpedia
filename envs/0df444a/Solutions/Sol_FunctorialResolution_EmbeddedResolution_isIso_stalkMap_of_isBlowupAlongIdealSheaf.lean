-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isIso_stalkMap_of_isBlowupAlongIdealSheaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:15:37.76967+00:00
-- url     : https://prove2.me/submissions/b29e3b60-029b-4faa-8825-4908caf54aa3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupIsoOffCenter
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_OrderUnderStalkIsomorphism
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_isIso_of_top
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_of_isIso
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_restrict
import Theorems.Thm_P2M_FunctorialResolution_Blowup_comap___support_compl_eq_top_7d133a646fc9


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
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData)
    (h : Blowup.IsBlowupAlongIdealSheaf π Z) (x : X₁) (hx : π.base x ∉ Z.support) :
    IsIso (π.stalkMap x) := by
  have h1 := h.restrict Z.support.compl
  rw [Blowup.comap_ι_support_compl_eq_top Z] at h1
  have hiso : IsIso (π ∣_ Z.support.compl) := h1.isIso_of_top
  have hoi : IsOpenImmersion (π ∣_ Z.support.compl) := IsOpenImmersion.of_isIso _
  have hxV : x ∈ π ⁻¹ᵁ Z.support.compl := hx
  let y : ↥((π ⁻¹ᵁ Z.support.compl).toScheme) := ⟨x, hxV⟩
  have hs2 : IsIso ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).stalkMap y) := inferInstance
  have hoi2 : IsOpenImmersion
      ((π ∣_ Z.support.compl) ≫ Scheme.Opens.ι Z.support.compl) := inferInstance
  have hB : IsIso (((π ∣_ Z.support.compl) ≫ Scheme.Opens.ι Z.support.compl).stalkMap y) :=
    inferInstance
  have hcomp : Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl) ≫ π
      = (π ∣_ Z.support.compl) ≫ Scheme.Opens.ι Z.support.compl :=
    (morphismRestrict_ι π Z.support.compl).symm
  have hA : IsIso ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl) ≫ π).stalkMap y) := by
    rw [hcomp]
    exact hB
  have e2 : (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl) ≫ π).stalkMap y
      = π.stalkMap ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).base y)
        ≫ (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).stalkMap y := Scheme.Hom.stalkMap_comp _ _ _
  have hC : IsIso (π.stalkMap ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).base y)
      ≫ (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).stalkMap y) := by
    rw [e2] at hA
    exact hA
  have hr : π.stalkMap ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).base y)
      = (π.stalkMap ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).base y)
          ≫ (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).stalkMap y)
        ≫ inv ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).stalkMap y) := by
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hfin : IsIso (π.stalkMap ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).base y)) := by
    rw [hr]
    infer_instance
  exact hfin
end FunctorialResolution.EmbeddedResolution
