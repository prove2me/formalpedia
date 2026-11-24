-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.inducedBlowups_transitionMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:03:28.114006+00:00
-- url     : https://prove2.me/submissions/d3c7db24-95ef-4972-b9ba-924b240b84f0

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_totalMapOfLE_self
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_totalMapOfLE_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_inducedBlowups_blowupMorphism
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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_blowupMorphism_eq_transitionMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_nontrivialIndex_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_transitionMap_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_transitionMap_trans
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

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (S : EmbeddedBlowupSequence k Y pY) (h : S.TransitionsAreBlowups) {a b : ℕ}
    (hab : a ≤ b) : (S.inducedBlowups h).transitionMap hab = S.totalMapOfLE hab := by
  induction b, hab using Nat.le_induction with
  | base =>
      have h1 : (S.inducedBlowups h).transitionMap (Nat.le_refl a) = 𝟙 ((S.inducedBlowups h).tower.obj (op a)) :=
        (SequenceOfBlowups.transitionMap_def (S.inducedBlowups h) (Nat.le_refl a)).trans
          ((S.inducedBlowups h).tower.map_id (op a))
      exact h1.trans (S.totalMapOfLE_self a).symm
  | succ b hb ih =>
      have e1 : (S.inducedBlowups h).transitionMap (hb.trans (Nat.le_succ b))
          = (S.inducedBlowups h).transitionMap (Nat.le_succ b) ≫ (S.inducedBlowups h).transitionMap hb :=
        (SequenceOfBlowups.transitionMap_trans (S.inducedBlowups h) hb (Nat.le_succ b)).symm
      have e2 : (S.inducedBlowups h).transitionMap (Nat.le_succ b) = S.totalTransition b :=
        (SequenceOfBlowups.blowupMorphism_eq_transitionMap (S.inducedBlowups h) b).symm.trans (inducedBlowups_blowupMorphism S h b)
      have e3 : S.totalMapOfLE (hb.trans (Nat.le_succ b)) = S.totalTransition b ≫ S.totalMapOfLE hb :=
        S.totalMapOfLE_succ hb
      have e4 : (S.inducedBlowups h).transitionMap (Nat.le_succ b) ≫ (S.inducedBlowups h).transitionMap hb
          = S.totalTransition b ≫ S.totalMapOfLE hb := by
        rw [e2, ih]
        exact rfl
      exact (e1.trans e4).trans e3.symm
end FunctorialResolution.EmbeddedResolution
