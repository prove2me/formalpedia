-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.restrictIdeal_comap_preimage_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:00:36.55286+00:00
-- url     : https://prove2.me/submissions/f8d8d988-bf51-41ad-9a1b-8cc6a24dbd3a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsChartNormalization
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
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {Y Y' : Scheme.{u}} (f : Y' ⟶ Y) (V : Y.Opens)
    (D : Y.IdealSheafData) (h : restrictIdeal D V = ⊤) :
    restrictIdeal (D.comap f) (f ⁻¹ᵁ V) = ⊤ := by
  have h1 : restrictIdeal (D.comap f) (f ⁻¹ᵁ V)
      = (restrictIdeal D V).comap (morphismRestrict f V) := by
    rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
      ← morphismRestrict_ι, Scheme.IdealSheafData.comap_comp]
  rw [h1, h, Scheme.IdealSheafData.comap_top]
end FunctorialResolution.EmbeddedResolution
