-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.prodMapOnPreimage_comp_projRight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:50:16.560987+00:00
-- url     : https://prove2.me/submissions/3438bdd5-6b88-4861-b12d-6758f6c4790c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceProduct
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_homOfSumCoords_appTop_coord_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_homOfSumCoords_appTop_coord_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_sumUliftEquivUliftSum_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_sumUliftEquivUliftSum_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_sumUliftEquivUliftSum_symm_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_sumUliftEquivUliftSum_symm_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_projRight_comp_affineSpaceIndexedByToSpec
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_projRight_appTop_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_projLeft_comp_affineSpaceIndexedByToSpec
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_projLeft_appTop_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_prodMapOnPreimage_comp_affineSpaceIndexedByToSpec
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def


attribute [local simp] FunctorialResolution.EmbeddedResolution.homOfSumCoords_appTop_coord_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.homOfSumCoords_appTop_coord_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.sumUliftEquivUliftSum_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.sumUliftEquivUliftSum_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.sumUliftEquivUliftSum_symm_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.sumUliftEquivUliftSum_symm_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.projRight_comp_affineSpaceIndexedByToSpec
attribute [local simp] FunctorialResolution.EmbeddedResolution.projRight_appTop_coord
attribute [local simp] FunctorialResolution.EmbeddedResolution.projLeft_comp_affineSpaceIndexedByToSpec
attribute [local simp] FunctorialResolution.EmbeddedResolution.projLeft_appTop_coord

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (n m c : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens)
    (φ : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c))) :
    prodMapOnPreimage k n m c U φ ≫ projRight k c m =
      (projLeft k n m ⁻¹ᵁ U).ι ≫ projRight k n m := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, projRight_comp_affineSpaceIndexedByToSpec, Category.assoc, projRight_comp_affineSpaceIndexedByToSpec, prodMapOnPreimage_comp_affineSpaceIndexedByToSpec]
  · rintro ⟨j⟩
    simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    rw [projRight_appTop_coord, projRight_appTop_coord]
    simp [prodMapOnPreimage]
end FunctorialResolution.EmbeddedResolution
