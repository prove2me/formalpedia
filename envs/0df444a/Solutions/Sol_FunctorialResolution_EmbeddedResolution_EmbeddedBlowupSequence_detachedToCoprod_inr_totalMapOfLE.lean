-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.detachedToCoprod_inr_totalMapOfLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:07:11.012058+00:00
-- url     : https://prove2.me/submissions/dcca2a97-df3c-4017-bfe2-ea84e6eb4936

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_detachedCoprodInl_inr_totalTransition_assoc
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_detachedCoprodInr_inr_totalTransition_assoc
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_detachedToCoprod_succ_of_lt
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_detachedToCoprod_self
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_totalMapOfLE_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_inl_totalMapOfLE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
namespace EmbeddedBlowupSequence
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
variable (S : EmbeddedBlowupSequence k Y pY)
private theorem detachedToCoprod_inr_totalMapOfLE_forall (W : EmbeddedBlowupSequence k Y pY) :
    ∀ (b a s : ℕ) (hab : a ≤ b) (has : a ≤ s) (hsb : s < b),
      W.detachedToCoprod s b hsb ≫ (coprod.inr : W.detachedCoprod b ⟶ W.totalSpace b) ≫ W.totalMapOfLE hab =
        W.detachedι s ≫ W.strictTransformMapOfLE has ≫ (coprod.inl : W.strictTransform a ⟶ W.totalSpace a) := by
  intro b
  induction b with
  | zero => exact fun a s _ _ hsb => absurd hsb (Nat.not_lt_zero s)
  | succ b ih =>
      intro a s hab has hsb
      by_cases h : s = b
      · subst h
        have hd : W.totalMapOfLE hab = W.totalTransition s ≫ W.totalMapOfLE has := W.totalMapOfLE_succ has
        have hfs : W.detachedToCoprod s (s + 1) hsb = W.detachedCoprodInr s := W.detachedToCoprod_self s
        rw [hfs, hd, W.detachedCoprodInr_inr_totalTransition_assoc s (W.totalMapOfLE has),
          W.inl_totalMapOfLE has]
      · have hsb' : s < b := lt_of_le_of_ne (Nat.lt_succ_iff.mp hsb) h
        have hab' : a ≤ b := has.trans hsb'.le
        have hd : W.totalMapOfLE hab = W.totalTransition b ≫ W.totalMapOfLE hab' := W.totalMapOfLE_succ hab'
        have hf : W.detachedToCoprod s (b + 1) hsb = W.detachedToCoprod s b hsb' ≫ W.detachedCoprodInl b :=
          W.detachedToCoprod_succ_of_lt s b hsb'
        rw [hf, hd, Category.assoc,
          W.detachedCoprodInl_inr_totalTransition_assoc b (W.totalMapOfLE hab')]
        exact ih a s hab' has hsb'
end EmbeddedBlowupSequence
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
end FunctorialResolution.EmbeddedResolution
end
end

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
theorem _root_.solution {a b s : ℕ} (hab : a ≤ b) (has : a ≤ s) (hsb : s < b) :
    S.detachedToCoprod s b hsb ≫ (coprod.inr : S.detachedCoprod b ⟶ S.totalSpace b) ≫ S.totalMapOfLE hab =
      S.detachedι s ≫ S.strictTransformMapOfLE has ≫ (coprod.inl : S.strictTransform a ⟶ S.totalSpace a) :=
  detachedToCoprod_inr_totalMapOfLE_forall S b a s hab has hsb
end FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence
