-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inl_totalTransition_assoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:32:26.979401+00:00
-- url     : https://prove2.me/submissions/4a9d35e4-654e-4346-ae63-22e25ff91cea

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_inl_totalTransition_eq_strictTransformMap_inl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (i : ℕ) {T : Scheme.{u}} (g : S.totalSpace i ⟶ T) :
    (coprod.inl : S.strictTransform (i + 1) ⟶ S.totalSpace (i + 1)) ≫ S.totalTransition i ≫ g =
      S.strictTransformMap i ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) ≫ g := by
  rw [← Category.assoc, S.inl_totalTransition_eq_strictTransformMap_inl i, Category.assoc]
end FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence
