-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.comap_coordIdeal_singleton_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:20:08.23058+00:00
-- url     : https://prove2.me/submissions/56446db8-755e-46bd-a379-007d13fad9cc

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateSubstitution
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_comap_coordBlowupSubstMap_coordSubspaceIdeal_singleton_of_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_comap_coordIdeal_of_coordBlowupSubstMap
import Theorems.Thm_P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul_ffd4b47c5064b9ee


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
    (hg : c₁.map ≫ coordBlowupSubstMap k m S s = g ≫ c.map)
    (j : Fin m) (hj : j ∈ S) (hjs : j ≠ s) :
    (c.coordIdeal {j}).comap g = c₁.coordIdeal {j} * c₁.coordIdeal {s} := by
  rw [comap_coordIdeal_of_coordBlowupSubstMap c c₁ g hg {j},
    comap_coordBlowupSubstMap_coordSubspaceIdeal_singleton_of_mem k m S s j hj hjs,
    Scheme.IdealSheafData.comap_mul]
  rfl
end FunctorialResolution.EmbeddedResolution
