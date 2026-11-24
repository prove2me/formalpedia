-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.totalSpaceZeroIso_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:59:09.369987+00:00
-- url     : https://prove2.me/submissions/864c80db-f175-43cd-b09a-96d65bdce0ea

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_strictTransformZeroIso_hom_emb
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_totalSpaceZeroIso_spec
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_totalSpaceZeroIso_spec


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
theorem _root_.solution :
    S.totalSpaceZeroIso.inv =
      S.strictTransformZeroIso.inv ≫ (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) := by
  have h2 : S.strictTransformZeroIso.hom ≫ (S.emb ≫ S.ambientSeq.isoZero.inv) = S.strictTransformι 0 := by
    rw [← Category.assoc, S.strictTransformZeroIso_hom_emb, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h3 : (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom =
      S.strictTransformZeroIso.hom := by
    refine (cancel_mono (S.emb ≫ S.ambientSeq.isoZero.inv)).mp ?_
    rw [Category.assoc, S.totalSpaceZeroIso_spec, h2]
  refine (cancel_mono S.totalSpaceZeroIso.hom).mp ?_
  rw [Iso.inv_hom_id, Category.assoc, h3, Iso.inv_hom_id]
end FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence
