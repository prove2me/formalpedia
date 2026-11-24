-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.embeddedResolutionRuleOfPrincipalization_affineSpaceEmbeddingDatum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:53:18.91383+00:00
-- url     : https://prove2.me/submissions/ee277054-aa33-4fad-b9a4-7951c181919a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_RemoveIsoBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_EmbeddedResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FunctorialPrincipalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedStrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedBlowupSequence
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_embeddedInducedBlowupsWithoutIso_eq
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_embeddedResolutionRuleOfPrincipalization_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_affineSpaceEmbeddingDatum_toEmbeddedBlowupSequence

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
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (A : PrincipalizationAlgorithm.{u}) (h : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hw : EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm)
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] :
    embeddedResolutionRuleOfPrincipalization A h k Y pY (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) =
      affineResolutionRuleOfPrincipalization A hemb hsnc hsm hw k Y pY := by
  have hT := affineSpaceEmbeddingDatum_toEmbeddedBlowupSequence A hemb hsnc hsm k Y pY
  have key : ∀ (T₁ T₂ : EmbeddedBlowupSequence k Y pY), T₁ = T₂ →
      ∀ (h₁ : T₁.TransitionsAreBlowups) (h₂ : T₂.TransitionsAreBlowups),
        T₁.inducedBlowupsWithoutIso h₁ = T₂.inducedBlowupsWithoutIso h₂ := by
    rintro T₁ T₂ rfl h₁ h₂
    rfl
  calc embeddedResolutionRuleOfPrincipalization A h k Y pY (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY)
      = ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A).inducedBlowupsWithoutIso
          (h k Y pY (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY)) :=
        embeddedResolutionRuleOfPrincipalization_apply A h k Y pY (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY)
    _ = ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence).inducedBlowupsWithoutIso
          ((AffineSpacePrincipalizationData.toEmbeddedBlowupSequence_transitionsAreBlowups_iff
            (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)).mpr (hw k Y pY)) :=
        key _ _ hT _ _
    _ = (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).blowupSequenceWithoutIsos (hw k Y pY) :=
        AffineSpacePrincipalizationData.embeddedInducedBlowupsWithoutIso_eq (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)
          (hw k Y pY)
    _ = affineResolutionRuleOfPrincipalization A hemb hsnc hsm hw k Y pY := rfl
end FunctorialResolution.EmbeddedResolution
