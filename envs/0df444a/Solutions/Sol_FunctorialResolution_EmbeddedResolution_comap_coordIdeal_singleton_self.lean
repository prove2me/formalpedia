-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.comap_coordIdeal_singleton_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:01:24.409564+00:00
-- url     : https://prove2.me/submissions/20d6df00-4f41-483b-8e77-25898b80eaed

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateSubstitution
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_comap_coordBlowupSubstMap_coordSubspaceIdeal_singleton_self
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_comap_coordIdeal_of_coordBlowupSubstMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {p₁ : X₁ ⟶ Spec (CommRingCat.of k)}
    {U : X.Opens} {V : X₁.Opens} {m : ℕ} {S : Finset (Fin m)} {s : Fin m}
    (c : EtaleChart p U m) (c₁ : EtaleChart p₁ V m)
    (g : V.toScheme ⟶ U.toScheme)
    (hg : c₁.map ≫ coordBlowupSubstMap k m S s = g ≫ c.map) :
    (c.coordIdeal {s}).comap g = c₁.coordIdeal {s} := by
  rw [comap_coordIdeal_of_coordBlowupSubstMap c c₁ g hg {s},
    comap_coordBlowupSubstMap_coordSubspaceIdeal_singleton_self k m S s]
  rfl
end FunctorialResolution.EmbeddedResolution
