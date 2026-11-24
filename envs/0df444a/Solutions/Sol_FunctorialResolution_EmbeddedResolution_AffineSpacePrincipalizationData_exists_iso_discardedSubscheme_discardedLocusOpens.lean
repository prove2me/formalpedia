-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.exists_iso_discardedSubscheme_discardedLocusOpens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:51:53.465764+00:00
-- url     : https://prove2.me/submissions/f4a74b07-9a09-4f9c-9105-48bbb7ee40b3

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_coe_discardedLocusClosure
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_discardedIdeal_eq_vanishingIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_isClosed_discardedLocus
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_iso_subscheme_vanishingIdeal_of_isClosed

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
private theorem exists_iso_subscheme_of_ideal_eq {X : Scheme.{u}} {J J' : X.IdealSheafData} (h : J = J')
    {T : Scheme.{u}} (f : T ⟶ X)
    (he : ∃ e : J'.subscheme ≅ T, e.hom ≫ f = J'.subschemeι) :
    ∃ e : J.subscheme ≅ T, e.hom ≫ f = J.subschemeι := by
  subst h
  exact he
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
theorem _root_.solution (i : ℕ)
    [AlgebraicGeometry.IsReduced (S.strictTransform i)]
    (hN : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i))
    (hopen : IsOpen (S.discardedLocus i)) :
    ∃ e : S.discardedSubscheme i ≅ Scheme.Opens.toScheme (S.discardedLocusOpens i hopen),
      e.hom ≫ Scheme.Opens.ι (S.discardedLocusOpens i hopen) = S.discardedι i := by
  have := hN
  have hC : IsClosed ((S.discardedLocusOpens i hopen : (S.strictTransform i).Opens) :
      Set ↥(S.strictTransform i)) := S.isClosed_discardedLocus i
  have hIeq : S.discardedIdeal i
      = Scheme.IdealSheafData.vanishingIdeal
          (⟨((S.discardedLocusOpens i hopen : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)), hC⟩ :
            TopologicalSpace.Closeds ↥(S.strictTransform i)) := by
    rw [S.discardedIdeal_eq_vanishingIdeal i]
    congr 1
    exact TopologicalSpace.Closeds.ext (S.coe_discardedLocusClosure i)
  exact exists_iso_subscheme_of_ideal_eq hIeq _
    (exists_iso_subscheme_vanishingIdeal_of_isClosed (S.discardedLocusOpens i hopen) hC)
end FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData
