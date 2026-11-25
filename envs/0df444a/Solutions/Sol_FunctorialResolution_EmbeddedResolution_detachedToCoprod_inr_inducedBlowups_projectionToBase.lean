-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.detachedToCoprod_inr_inducedBlowups_projectionToBase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:21:42.124351+00:00
-- url     : https://prove2.me/submissions/35b71672-024a-493c-8185-d50c16703d8a

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_inl_totalSpaceZeroIso_hom
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_totalMapOfLE_self
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_detachedToCoprod_inr_totalMapOfLE
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_detachedCoprodMapOfLE_self
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_inducedBlowups_transitionMap
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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_projectionToBase_def
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


attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.totalMapOfLE_self
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.detachedCoprodMapOfLE_self

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (S : EmbeddedBlowupSequence k Y pY) (h : S.TransitionsAreBlowups)
    (s i : ℕ) (hs : s < i) :
    S.detachedToCoprod s i hs ≫ (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫
        (S.inducedBlowups h).projectionToBase i =
      S.detachedι s ≫ S.strictTransformToBase s := by
  have hdown : (S.inducedBlowups h).transitionMap (Nat.zero_le i) = S.totalMapOfLE (Nat.zero_le i) :=
    inducedBlowups_transitionMap S h (Nat.zero_le i)
  have hstruct : (S.inducedBlowups h).projectionToBase i
      = S.totalMapOfLE (Nat.zero_le i) ≫ S.totalSpaceZeroIso.hom :=
    Eq.trans (SequenceOfBlowups.projectionToBase_def (S.inducedBlowups h) i)
      (congrArg (fun t : S.totalSpace i ⟶ S.totalSpace 0 => t ≫ S.totalSpaceZeroIso.hom) hdown)
  have hkey := S.detachedToCoprod_inr_totalMapOfLE (Nat.zero_le i) (Nat.zero_le s) hs
  calc S.detachedToCoprod s i hs ≫ (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫
        (S.inducedBlowups h).projectionToBase i
      = (S.detachedToCoprod s i hs ≫ (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫
          S.totalMapOfLE (Nat.zero_le i)) ≫ S.totalSpaceZeroIso.hom := by
        rw [hstruct]; simp only [Category.assoc]
    _ = (S.detachedι s ≫ S.strictTransformMapOfLE (Nat.zero_le s) ≫
          (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0)) ≫ S.totalSpaceZeroIso.hom := by
        rw [hkey]
    _ = S.detachedι s ≫ S.strictTransformMapOfLE (Nat.zero_le s) ≫
          ((coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom) := by
        simp only [Category.assoc]
    _ = S.detachedι s ≫ S.strictTransformMapOfLE (Nat.zero_le s) ≫ S.strictTransformZeroIso.hom := by
        rw [S.inl_totalSpaceZeroIso_hom]
    _ = S.detachedι s ≫ S.strictTransformToBase s := rfl
end FunctorialResolution.EmbeddedResolution
