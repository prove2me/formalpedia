-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsStrictNormalCrossingsDivisor.reducedInverseImage_coprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:18:34.615005+00:00
-- url     : https://prove2.me/submissions/bc3334fa-8a5d-4f36-b8f0-b4586f2f811e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsOpenImmersion
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isStrictNormalCrossingsAt_base_of_comap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_comap_reducedInverseImage_of_isOpenImmersion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
namespace IsStrictNormalCrossingsDivisor
theorem _root_.solution {A B Z : Scheme.{u}} (g : (A ⨿ B) ⟶ Z)
    (W : TopologicalSpace.Closeds Z)
    (hA : IsStrictNormalCrossingsDivisor (reducedInverseImage ((coprod.inl : A ⟶ A ⨿ B) ≫ g) W))
    (hB : IsStrictNormalCrossingsDivisor (reducedInverseImage ((coprod.inr : B ⟶ A ⨿ B) ≫ g) W)) :
    IsStrictNormalCrossingsDivisor (reducedInverseImage g W) := by
  intro z
  by_cases hz : z ∈ Set.range ⇑(coprod.inl : A ⟶ A ⨿ B).base
  · obtain ⟨a, rfl⟩ := hz
    have h1 : (reducedInverseImage g W).comap (coprod.inl : A ⟶ A ⨿ B)
        = reducedInverseImage ((coprod.inl : A ⟶ A ⨿ B) ≫ g) W :=
      comap_reducedInverseImage_of_isOpenImmersion _ g W
    refine isStrictNormalCrossingsAt_base_of_comap (coprod.inl : A ⟶ A ⨿ B) (reducedInverseImage g W) ?_ a
    rw [h1]
    exact hA
  · have hz' : z ∈ Set.range ⇑(coprod.inr : B ⟶ A ⨿ B).base := by
      rw [Blowup.range_coprod_inr_eq_compl]
      exact hz
    obtain ⟨b, rfl⟩ := hz'
    have h1 : (reducedInverseImage g W).comap (coprod.inr : B ⟶ A ⨿ B)
        = reducedInverseImage ((coprod.inr : B ⟶ A ⨿ B) ≫ g) W :=
      comap_reducedInverseImage_of_isOpenImmersion _ g W
    refine isStrictNormalCrossingsAt_base_of_comap (coprod.inr : B ⟶ A ⨿ B) (reducedInverseImage g W) ?_ b
    rw [h1]
    exact hB
end IsStrictNormalCrossingsDivisor
end FunctorialResolution.EmbeddedResolution
