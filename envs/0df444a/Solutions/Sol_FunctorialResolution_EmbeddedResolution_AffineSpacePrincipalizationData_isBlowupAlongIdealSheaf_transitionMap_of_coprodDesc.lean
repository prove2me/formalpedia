-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.isBlowupAlongIdealSheaf_transitionMap_of_coprodDesc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:17:30.689252+00:00
-- url     : https://prove2.me/submissions/1f73fcf8-4c19-4a11-8fa3-e7ce7dda3958

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ClopenSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ReducedSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FunctorialPrincipalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedStrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_DiscardedLocus
import Theorems.Thm_FunctorialResolution_Blowup_isBlowupAlongIdealSheaf_id_top
import Theorems.Thm_FunctorialResolution_Blowup_ker_comp_coprod_inl_comap_inl
import Theorems.Thm_FunctorialResolution_Blowup_ker_comp_coprod_inl_comap_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_blowupSequence_center
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_blowupSequence_length
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_blowupSequence_tower
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_centerOnTotalSpace_eq_ker
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_discardedUnion_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_discardedUnion_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_strictTransformIdeal_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_strictTransformIdeal_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_nontrivialIndex_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_center
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_length
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_schemeAt
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coe_complOpensOfIsClosed
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isBlowupAlongIdealSheaf_of_isIso_comp
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.blowupSequence_center
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.blowupSequence_length
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.blowupSequence_tower
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.discardedUnion_succ
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.discardedUnion_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.strictTransformIdeal_succ
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.strictTransformIdeal_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.nontrivialIndex_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_center
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_length
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_schemeAt
attribute [local simp] FunctorialResolution.EmbeddedResolution.coe_complOpensOfIsClosed
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def


section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem isIso_coprodSwapAssocHom (A F G : Scheme.{u}) :
    CategoryTheory.IsIso (coprodSwapAssocHom A F G) := by
  refine ⟨⟨coprodSwapAssocInv A F G, ?_, ?_⟩⟩
  · refine coprod.hom_ext ?_ (coprod.hom_ext ?_ ?_) <;>
      simp only [coprodSwapAssocHom, coprodSwapAssocInv, Category.assoc, coprod.inl_desc,
        coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.comp_id]
  · refine coprod.hom_ext (coprod.hom_ext ?_ ?_) ?_ <;>
      simp only [coprodSwapAssocHom, coprodSwapAssocInv, Category.assoc, coprod.inl_desc,
        coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.comp_id]
private theorem isBlowupAlongIdealSheaf_coprodDesc_coprod {A B F G : Scheme.{u}} (a : A ⟶ B) (g : G ⟶ B)
    (K : B.IdealSheafData) (J : (B ⨿ F).IdealSheafData)
    (hinl : J.comap (coprod.inl : B ⟶ B ⨿ F) = K)
    (hinr : J.comap (coprod.inr : F ⟶ B ⨿ F) = ⊤)
    (h : Blowup.IsBlowupAlongIdealSheaf (coprod.desc a g) K) :
    Blowup.IsBlowupAlongIdealSheaf (coprod.desc (a ≫ (coprod.inl : B ⟶ B ⨿ F))
      (coprod.desc (coprod.inr : F ⟶ B ⨿ F) (g ≫ (coprod.inl : B ⟶ B ⨿ F)))) J := by
  have hmap : Blowup.IsBlowupAlongIdealSheaf (coprod.map (coprod.desc a g) (𝟙 F)) J := by
    refine Blowup.IsBlowupAlongIdealSheaf.coprod ?_ ?_
    · rw [hinl]
      exact h
    · rw [hinr]
      exact Blowup.isBlowupAlongIdealSheaf_id_top _
  have := isIso_coprodSwapAssocHom A F G
  have hfac : coprodSwapAssocHom A F G ≫ coprod.map (coprod.desc a g) (𝟙 F)
      = coprod.desc (a ≫ (coprod.inl : B ⟶ B ⨿ F))
        (coprod.desc (coprod.inr : F ⟶ B ⨿ F) (g ≫ (coprod.inl : B ⟶ B ⨿ F))) := by
    refine coprod.hom_ext ?_ (coprod.hom_ext ?_ ?_) <;>
      simp only [coprodSwapAssocHom, Category.assoc, coprod.inl_desc, coprod.inr_desc,
        coprod.inl_desc_assoc, coprod.inr_desc_assoc, coprod.inl_map, coprod.inr_map,
        Category.id_comp]
  exact isBlowupAlongIdealSheaf_of_isIso_comp _ _ (coprodSwapAssocHom A F G) hfac _ hmap
namespace AffineSpacePrincipalizationData
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
  (S : AffineSpacePrincipalizationData k Y pY)
end AffineSpacePrincipalizationData
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
  (S : AffineSpacePrincipalizationData k Y pY)
namespace FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData
theorem _root_.solution (i : ℕ)
    (h : Blowup.IsBlowupAlongIdealSheaf (coprod.desc (S.strictTransformMap i) (S.discardedι i)) (S.centerOffDetached i)) :
    Blowup.IsBlowupAlongIdealSheaf (S.transitionMap i) (S.centerOnTotalSpace i) := by
  have hq1 : AlgebraicGeometry.QuasiCompact (S.centerOffDetached i).subschemeι := inferInstance
  have hq2 : AlgebraicGeometry.QuasiCompact ((S.centerOffDetached i).subschemeι ≫
      (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)) := by
    have : AlgebraicGeometry.QuasiCompact
        (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) := Blowup.instQuasiCompactCoprodInl _ _
    infer_instance
  have hinl : (S.centerOnTotalSpace i).comap (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)
      = S.centerOffDetached i := by
    rw [S.centerOnTotalSpace_eq_ker i, Blowup.ker_comp_coprod_inl_comap_inl,
      Scheme.IdealSheafData.ker_subschemeι]
  have hinr : (S.centerOnTotalSpace i).comap (coprod.inr : S.discardedUnion i ⟶ S.totalSpace i) = ⊤ := by
    rw [S.centerOnTotalSpace_eq_ker i]
    exact Blowup.ker_comp_coprod_inl_comap_inr _
  exact isBlowupAlongIdealSheaf_coprodDesc_coprod (S.strictTransformMap i) (S.discardedι i) (S.centerOffDetached i) (S.centerOnTotalSpace i)
    hinl hinr h
end FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData
