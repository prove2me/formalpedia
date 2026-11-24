-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.isReduced_strictTransform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:33:45.758833+00:00
-- url     : https://prove2.me/submissions/72bad2f6-0722-4e04-b2c5-699323c60389

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_isBlowupAlongIdealSheaf_blowupMorphism
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isReduced_subscheme_ker
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isReduced_subscheme_strictTransform

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution [AlgebraicGeometry.IsReduced Y]
    (hN : ∀ j, j ≤ S.ambientLength → AlgebraicGeometry.IsNoetherian (S.ambientLevel j))
    (j : ℕ) (hj : j ≤ S.ambientLength) :
    AlgebraicGeometry.IsReduced (S.strictTransform j) := by
  revert hj
  induction j with
  | zero =>
    intro _
    have := S.emb_closedImmersion
    have hq : AlgebraicGeometry.QuasiCompact (S.emb ≫ S.ambientBlowups.isoZero.inv) := inferInstance
    exact isReduced_subscheme_ker (S.emb ≫ S.ambientBlowups.isoZero.inv)
  | succ n ih =>
    intro hj
    have hn : n < S.ambientLength := Nat.lt_of_succ_le hj
    have : AlgebraicGeometry.IsReduced (S.strictTransformIdeal n).subscheme := ih (le_of_lt hn)
    have hNoeth : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel (n + 1)) := by
      have : AlgebraicGeometry.IsNoetherian (S.ambientLevel (n + 1)) := hN (n + 1) hj
      infer_instance
    have : AlgebraicGeometry.QuasiCompact
        (EmbeddedResolution.strictTransformι (S.ambientBlowupMorphism n) (S.ambientCenter n) (S.strictTransformIdeal n)) :=
      quasiCompact_strictTransformι_of_noetherianSpace_source _ _ _ hNoeth
    exact isReduced_subscheme_strictTransform (S.ambientBlowupMorphism n) (S.ambientCenter n)
      (S.strictTransformIdeal n) (S.ambientBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn)
end FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData
