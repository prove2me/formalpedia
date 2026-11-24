-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsStrictNormalCrossingsDivisor.of_isOpenImmersion_jointly_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:47:32.404844+00:00
-- url     : https://prove2.me/submissions/52cba20b-10ea-4cf1-8fef-d67c149dcc2e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsOpenImmersion
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isStrictNormalCrossingsAt_base_of_comap

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
theorem _root_.solution {X : Scheme.{u}} (D : X.IdealSheafData) {ι : Type v}
    (Y : ι → Scheme.{u}) (p : ∀ i, Y i ⟶ X) (hp : ∀ i, IsOpenImmersion (p i))
    (hsurj : ∀ x : X, ∃ (i : ι) (y : Y i), (p i).base y = x)
    (hD : ∀ i, IsStrictNormalCrossingsDivisor (D.comap (p i))) : IsStrictNormalCrossingsDivisor D := by
  intro x
  obtain ⟨i, y, hy⟩ := hsurj x
  subst hy
  have := hp i
  exact isStrictNormalCrossingsAt_base_of_comap (p i) D (hD i) y
end IsStrictNormalCrossingsDivisor
end FunctorialResolution.EmbeddedResolution
