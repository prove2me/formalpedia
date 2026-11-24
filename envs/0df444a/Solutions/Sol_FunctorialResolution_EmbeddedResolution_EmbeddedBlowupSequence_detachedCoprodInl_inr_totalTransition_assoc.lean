-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.detachedCoprodInl_inr_totalTransition_assoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:00:43.41818+00:00
-- url     : https://prove2.me/submissions/b47c7e62-bcce-4138-b111-b762332dbe05

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedStrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrictTransformTower
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_detachedCoprodInl_inr_totalTransition
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_blowupSequence_center
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_blowupSequence_length
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_blowupSequence_tower
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_discardedUnion_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_discardedUnion_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_strictTransformIdeal_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_strictTransformIdeal_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_detachedCoprod_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_detachedCoprod_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_inducedBlowups_center
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_inducedBlowups_length
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_inducedBlowups_tower
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_strictTransformIdeal_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_strictTransformIdeal_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedResolutionRule_toAffineResolutionRule_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_nontrivialIndex_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_center
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_length
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_schemeAt
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
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.blowupSequence_center
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.blowupSequence_length
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.blowupSequence_tower
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.discardedUnion_succ
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.discardedUnion_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.strictTransformIdeal_succ
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.strictTransformIdeal_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.detachedCoprod_succ
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.detachedCoprod_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_center
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_tower
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.strictTransformIdeal_succ
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.strictTransformIdeal_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedResolutionRule.toAffineResolutionRule_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.nontrivialIndex_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_center
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_length
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_schemeAt
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def



set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
variable (S : EmbeddedBlowupSequence k Y pY)
namespace FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence
theorem _root_.solution (i : ℕ) {T : Scheme.{u}}
    (g : S.totalSpace i ⟶ T) :
    S.detachedCoprodInl i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
        S.totalTransition i ≫ g =
      (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫ g := by
  have h : S.detachedCoprodInl i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
      S.totalTransition i = (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) :=
    S.detachedCoprodInl_inr_totalTransition i
  calc S.detachedCoprodInl i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
        S.totalTransition i ≫ g
      = (S.detachedCoprodInl i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
          S.totalTransition i) ≫ g := by simp only [Category.assoc]
    _ = (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫ g := by rw [h]
end FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence
