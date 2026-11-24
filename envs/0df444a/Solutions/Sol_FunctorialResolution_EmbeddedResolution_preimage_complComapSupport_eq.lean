-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.preimage_complComapSupport_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:50:15.233334+00:00
-- url     : https://prove2.me/submissions/dcd086f3-06be-412b-b09f-8a7d742f82b9

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransformOffCenter
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_StrictTransformClosedImmersion
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_map_eq_ker_subscheme__comp_8e2f1045f336
import Theorems.Thm_FunctorialResolution_Blowup_comap_map_of_isClosedImmersion
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coe_complComapSupport


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
theorem _root_.solution {A A' A₁ A'₁ : Scheme.{u}} (j : A ⟶ A') [IsClosedImmersion j]
    (Z : A.IdealSheafData) (π : A₁ ⟶ A) (π' : A'₁ ⟶ A') (j₁ : A₁ ⟶ A'₁)
    (hsq : j₁ ≫ π' = π ≫ j) :
    (Opens.map j₁.base).obj (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))) =
      complComapSupport π Z := by
  have key : ((Scheme.Hom.ker (Z.subschemeι ≫ j)).comap π').comap j₁ = Z.comap π := by
    rw [← Scheme.IdealSheafData.comap_comp, hsq, Scheme.IdealSheafData.comap_comp,
      ← map_eq_ker_subschemeι_comp, Blowup.comap_map_of_isClosedImmersion]
  have h2 : ((Z.comap π).support : Set A₁)
      = ⇑j₁.base ⁻¹'
        ((((Scheme.Hom.ker (Z.subschemeι ≫ j)).comap π').support : Set A'₁)) := by
    rw [← key, Scheme.IdealSheafData.support_comap
      ((Scheme.Hom.ker (Z.subschemeι ≫ j)).comap π') j₁]
    rfl
  apply TopologicalSpace.Opens.ext
  have h1 : (((Opens.map j₁.base).obj
        (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j)))) : Set A₁)
      = ⇑j₁.base ⁻¹' (((Scheme.Hom.ker (Z.subschemeι ≫ j)).comap π').support : Set A'₁)ᶜ := rfl
  rw [h1, coe_complComapSupport, h2, Set.preimage_compl]
end FunctorialResolution.EmbeddedResolution
