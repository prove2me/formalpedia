-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.strictTransformToBase_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:42:13.258051+00:00
-- url     : https://prove2.me/submissions/8163f0f6-2a80-4299-a327-3c25312c897b

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
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_strictTransformMapOfLE_strictTransform__a3eda6dd338c
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_strictTransformZeroIso_hom_emb
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_projectionToBase_def


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
theorem _root_.solution (i : ℕ) :
    S.strictTransformToBase i ≫ S.emb = S.strictTransformι i ≫ S.ambientSeq.projectionToBase i := by
  have h1 : S.strictTransformToBase i = S.strictTransformMapOfLE (Nat.zero_le i) ≫ S.strictTransformZeroIso.hom := rfl
  have h2 : S.ambientSeq.projectionToBase i
      = S.ambientSeq.transitionMap (Nat.zero_le i) ≫ S.ambientSeq.isoZero.hom :=
    SequenceOfBlowups.projectionToBase_def S.ambientSeq i
  rw [h1, Category.assoc, S.strictTransformZeroIso_hom_emb, ← Category.assoc,
    S.strictTransformMapOfLE_strictTransformι (Nat.zero_le i), Category.assoc, h2]
end FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence
