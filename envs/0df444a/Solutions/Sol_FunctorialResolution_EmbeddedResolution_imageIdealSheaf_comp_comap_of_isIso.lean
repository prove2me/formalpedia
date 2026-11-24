-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.imageIdealSheaf_comp_comap_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:49:14.069827+00:00
-- url     : https://prove2.me/submissions/09874d87-2abc-4814-b58d-e1298d444d09

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_IsomorphismTransport
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_imageIdealSheaf_eq_comap_inv
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_imageIdealSheaf_comap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_ker_comp_eq_imageIdealSheaf_ker
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_imageIdealSheaf_eq_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem exists_iso_subscheme_comap_of_isIso {A B : Scheme.{u}} (w : A ⟶ B) [IsIso w]
    (I : B.IdealSheafData) :
    ∃ θ : (I.comap w).subscheme ≅ I.subscheme,
      θ.hom ≫ I.subschemeι = (I.comap w).subschemeι ≫ w := by
  have e1 : ((I.comap w).subschemeι ≫ w).ker = I := by
    rw [ker_comp_eq_imageIdealSheaf_ker, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι,
      imageIdealSheaf_comap]
  have e2 : (I.subschemeι ≫ inv w).ker = I.comap w := by
    rw [ker_comp_eq_imageIdealSheaf_ker, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι,
      imageIdealSheaf_eq_comap_inv, IsIso.inv_inv]
  have h1 : I.subschemeι.ker ≤ ((I.comap w).subschemeι ≫ w).ker :=
    le_of_eq (by rw [e1, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι])
  have h2 : (I.comap w).subschemeι.ker ≤ (I.subschemeι ≫ inv w).ker :=
    le_of_eq (by rw [e2, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι])
  refine ⟨⟨IsClosedImmersion.lift I.subschemeι ((I.comap w).subschemeι ≫ w) h1,
    IsClosedImmersion.lift (I.comap w).subschemeι (I.subschemeι ≫ inv w) h2, ?_, ?_⟩, ?_⟩
  · rw [← cancel_mono (I.comap w).subschemeι, Category.assoc, IsClosedImmersion.lift_fac,
      ← Category.assoc, IsClosedImmersion.lift_fac, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id, Category.id_comp]
  · rw [← cancel_mono I.subschemeι, Category.assoc, IsClosedImmersion.lift_fac,
      ← Category.assoc, IsClosedImmersion.lift_fac, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id, Category.id_comp]
  · exact IsClosedImmersion.lift_fac ..
namespace IsPushforwardBlowupSeq
end IsPushforwardBlowupSeq
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {A B C : Scheme.{u}} (w : A ⟶ B) [IsIso w] (g : B ⟶ C)
    (I : B.IdealSheafData) :
    imageIdealSheaf (w ≫ g) (I.comap w) = imageIdealSheaf g I := by
  obtain ⟨θ, hθ⟩ := exists_iso_subscheme_comap_of_isIso w I
  rw [imageIdealSheaf_eq_ker (w ≫ g) (I.comap w), imageIdealSheaf_eq_ker g I, ← Category.assoc, ← hθ,
    Category.assoc, AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso]
end FunctorialResolution.EmbeddedResolution
