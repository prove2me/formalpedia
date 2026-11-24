-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inr_inr_totalTransition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:17:32.931966+00:00
-- url     : https://prove2.me/submissions/6da3bb68-db01-4d5b-98e9-9346fc111911

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
variable (T : EmbeddedBlowupSequence k Y pY)
namespace FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence
theorem _root_.solution (i : ℕ) :
    (coprod.inr : T.detachedScheme i ⟶ T.detachedCoprod (i + 1)) ≫
        (coprod.inr : T.detachedCoprod (i + 1) ⟶ T.totalSpace (i + 1)) ≫ T.totalTransition i =
      T.detachedι i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i) := by
  have h1 : (coprod.inr : T.detachedCoprod (i + 1) ⟶ T.totalSpace (i + 1)) ≫ T.totalTransition i =
      (coprod.desc (coprod.inr : T.detachedCoprod i ⟶ T.totalSpace i)
          (T.detachedι i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i)) :
        T.detachedCoprod i ⨿ T.detachedScheme i ⟶ T.totalSpace i) :=
    coprod.inr_desc _ _
  have h2 : (coprod.inr : T.detachedScheme i ⟶ T.detachedCoprod i ⨿ T.detachedScheme i) ≫
      (coprod.desc (coprod.inr : T.detachedCoprod i ⟶ T.totalSpace i)
          (T.detachedι i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i)) :
        T.detachedCoprod i ⨿ T.detachedScheme i ⟶ T.totalSpace i) =
      T.detachedι i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i) :=
    coprod.inr_desc _ _
  exact Eq.trans
    (congrArg
      (fun f : T.detachedCoprod (i + 1) ⟶ T.totalSpace i =>
        (coprod.inr : T.detachedScheme i ⟶ T.detachedCoprod (i + 1)) ≫ f) h1)
    h2
end FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence
