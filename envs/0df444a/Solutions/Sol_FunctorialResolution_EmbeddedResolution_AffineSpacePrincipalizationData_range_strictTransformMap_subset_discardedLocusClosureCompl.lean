-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.range_strictTransformMap_subset_discardedLocusClosureCompl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:52:00.22418+00:00
-- url     : https://prove2.me/submissions/61b9b28d-39e4-496c-86b8-5b0492ee0695

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_image_discardedLocus_subset_support
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_blowupSequence_center
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_blowupSequence_length
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_blowupSequence_tower
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_coe_discardedLocusClosure
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_coe_discardedLocusClosureCompl
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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_support_strictTransform_eq_closure_preimage
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_strictTransformMap_comp_strictTransform__d73a75e45c4a
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
private theorem noetherianSpace_of_isClosedImmersion {A B : Scheme.{u}} (f : A ⟶ B)
    [AlgebraicGeometry.IsClosedImmersion f]
    (h : TopologicalSpace.NoetherianSpace ↥B) : TopologicalSpace.NoetherianSpace ↥A := by
  have := h
  exact (Scheme.Hom.isClosedEmbedding f).toIsEmbedding.toIsInducing.noetherianSpace
private theorem noetherianSpace_of_isOpenImmersion {A B : Scheme.{u}} (f : A ⟶ B)
    [AlgebraicGeometry.IsOpenImmersion f]
    (h : TopologicalSpace.NoetherianSpace ↥B) : TopologicalSpace.NoetherianSpace ↥A := by
  have := h
  exact f.isOpenEmbedding.toIsEmbedding.toIsInducing.noetherianSpace
private theorem quasiCompact_strictTransformι_of_noetherianSpace_source {X X₁ : Scheme.{u}}
    (π : X₁ ⟶ X) (Z D : X.IdealSheafData) (h : TopologicalSpace.NoetherianSpace ↥X₁) :
    AlgebraicGeometry.QuasiCompact (strictTransformι π Z D) := by
  have := noetherianSpace_of_isOpenImmersion (Scheme.Opens.ι (strictTransformOpens π Z D))
    (noetherianSpace_of_isClosedImmersion (D.comap π).subschemeι h)
  infer_instance
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
theorem _root_.solution (i : ℕ) (_hi : i < S.ambientLength)
    (hN : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i))
    (hN' : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel (i + 1)))
    (hopen : IsOpen (S.discardedLocus i)) :
    Set.range ⇑(S.strictTransformMap i).base ⊆
      ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
  have := hN
  have hqc : AlgebraicGeometry.QuasiCompact
      (EmbeddedResolution.strictTransformι (S.ambientBlowupMorphism i) (S.ambientCenter i) (S.strictTransformIdeal i)) :=
    quasiCompact_strictTransformι_of_noetherianSpace_source _ _ _ hN'
  have hιemb : Topology.IsClosedEmbedding ⇑(S.strictTransformι i).base :=
    Scheme.Hom.isClosedEmbedding (S.strictTransformι i)
  have hUcoe : ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))
      = (S.discardedLocus i)ᶜ := by
    rw [S.coe_discardedLocusClosureCompl i, S.coe_discardedLocusClosure i]
  have hRclosed : IsClosed (⇑(S.strictTransformι i).base ''
      ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))) := by
    refine hιemb.isClosedMap _ ?_
    rw [hUcoe]
    exact hopen.isClosed_compl
  have hsub : (((S.strictTransformIdeal i).support : Set ↥(S.ambientLevel i)) \
        ((S.ambientCenter i).support : Set ↥(S.ambientLevel i)))
      ⊆ ⇑(S.strictTransformι i).base ''
        ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
    rintro w ⟨hw, hw'⟩
    have hw2 : w ∈ Set.range ⇑(S.strictTransformι i).base := by
      rw [Scheme.IdealSheafData.range_subschemeι (S.strictTransformIdeal i)]
      exact hw
    obtain ⟨z, rfl⟩ := hw2
    refine ⟨z, ?_, rfl⟩
    rw [hUcoe]
    intro hz
    exact hw' (S.image_discardedLocus_subset_support i ⟨z, hz, rfl⟩)
  have hcl : closure (⇑(S.ambientBlowupMorphism i).base ⁻¹'
        (((S.strictTransformIdeal i).support : Set ↥(S.ambientLevel i)) \
          ((S.ambientCenter i).support : Set ↥(S.ambientLevel i))))
      ⊆ ⇑(S.ambientBlowupMorphism i).base ⁻¹' (⇑(S.strictTransformι i).base ''
        ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))) :=
    closure_minimal (Set.preimage_mono hsub)
      (hRclosed.preimage (S.ambientBlowupMorphism i).base.hom.continuous)
  rintro _ ⟨x, rfl⟩
  have h1 : ⇑(S.strictTransformι (i + 1)).base x ∈
      ((S.strictTransformIdeal (i + 1)).support : Set ↥(S.ambientLevel (i + 1))) := by
    rw [← Scheme.IdealSheafData.range_subschemeι (S.strictTransformIdeal (i + 1))]
    exact Set.mem_range_self x
  rw [S.strictTransformIdeal_succ i, support_strictTransform_eq_closure_preimage] at h1
  have h2 := hcl h1
  have he : ⇑(S.strictTransformι i).base (⇑(S.strictTransformMap i).base x)
      = ⇑(S.ambientBlowupMorphism i).base (⇑(S.strictTransformι (i + 1)).base x) := by
    have h := congrArg (fun m : S.strictTransform (i + 1) ⟶ S.ambientLevel i => ⇑m.base x) (S.strictTransformMap_comp_strictTransformι i)
    simpa using h
  have h3 : ⇑(S.strictTransformι i).base (⇑(S.strictTransformMap i).base x) ∈
      ⇑(S.strictTransformι i).base ''
        ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
    rw [he]
    exact h2
  obtain ⟨z, hz, hzeq⟩ := h3
  have hzz : z = ⇑(S.strictTransformMap i).base x := hιemb.injective hzeq
  rw [← hzz]
  exact hz
end FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData
