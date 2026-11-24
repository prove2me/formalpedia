-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_restrict_coordIdeal_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:13:49.7768+00:00
-- url     : https://prove2.me/submissions/ee26d824-d0a2-4130-9aff-28a4014747d4

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_AffineSpaceSmooth
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordIdeal_eq_comap_coordSubspaceIdeal
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_comap___a4ce28546e44


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)} {m : ℕ}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {U V : X.Opens} (hVU : V ≤ U) (c : EtaleChart p U m)
    (Z : X.IdealSheafData) (S : Finset (Fin m)) (h : restrictIdeal Z U = c.coordIdeal S) :
    restrictIdeal Z V = (c.restrict hVU).coordIdeal S := by
  have h' : Z.comap U.ι = (coordSubspaceIdeal k m S).comap c.map := by
    rw [← restrictIdeal_eq_comap_ι, h, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  rw [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.restrict_map,
    Scheme.IdealSheafData.comap_comp, ← h', ← Scheme.IdealSheafData.comap_comp,
    Scheme.homOfLE_ι]
end FunctorialResolution.EmbeddedResolution
