-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.morphismRestrict_projLeft_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:50:11.972741+00:00
-- url     : https://prove2.me/submissions/bdc1e294-34a9-43ed-8979-e6d27eac2c57

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
    (φ : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c)))
    (hφ : φ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) =
      U.ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n))) :
    AlgebraicGeometry.morphismRestrict (projLeft k n m) U ≫ φ =
      prodMapOnPreimage k n m c U φ ≫ projLeft k c m := by
  refine AffineSpace.hom_ext ?_ ?_
  · have h1 : (AlgebraicGeometry.morphismRestrict (projLeft k n m) U ≫ φ) ≫
        affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) =
        (projLeft k n m ⁻¹ᵁ U).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) := by
      rw [Category.assoc, hφ, morphismRestrict_ι_assoc, projLeft_comp_affineSpaceIndexedByToSpec]
    have h2 : (prodMapOnPreimage k n m c U φ ≫ projLeft k c m) ≫
        affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) =
        (projLeft k n m ⁻¹ᵁ U).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) := by
      rw [Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec, prodMapOnPreimage_comp_affineSpaceIndexedByToSpec]
    exact h1.trans h2.symm
  · rintro ⟨j⟩
    have h : (prodMapOnPreimage k n m c U φ ≫ projLeft k c m).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)) =
        (AlgebraicGeometry.morphismRestrict (projLeft k n m) U ≫ φ).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)) := by
      rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply, projLeft_appTop_coord]
      simp [prodMapOnPreimage]
    exact h.symm
end FunctorialResolution.EmbeddedResolution
