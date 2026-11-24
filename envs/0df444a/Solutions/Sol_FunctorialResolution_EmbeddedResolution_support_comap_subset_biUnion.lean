-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.support_comap_subset_biUnion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:09:47.961795+00:00
-- url     : https://prove2.me/submissions/c9360de5-9e2e-4c90-a134-55b67ae3d48e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateSubstitution
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialPartAlongDivisor
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplitting
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplittingFlatPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_mem_support_comap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X Y : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (h : Y ⟶ X) (E : List X.IdealSheafData)
    (M : X.IdealSheafData) (hM : (M.support : Set X) ⊆ ⋃ D ∈ E, (D.support : Set X)) :
    ((M.comap h).support : Set Y) ⊆
      ⋃ D ∈ E.map (fun D : X.IdealSheafData => D.comap h), (D.support : Set Y) := by
  intro y hy
  have hy' : h.base y ∈ (M.support : Set X) := Scheme.IdealSheafData.mem_support_comap.mp hy
  obtain ⟨D, hD, hyD⟩ := Set.mem_iUnion₂.mp (hM hy')
  refine Set.mem_iUnion₂.mpr ⟨D.comap h, List.mem_map.mpr ⟨D, hD, rfl⟩, ?_⟩
  exact Scheme.IdealSheafData.mem_support_comap.mpr hyD
end FunctorialResolution.EmbeddedResolution
