-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.comap_coordBlowupSubstMap_coordSubspaceIdeal_singleton_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:47:37.026892+00:00
-- url     : https://prove2.me/submissions/f609df84-3105-4dc1-afbd-7109d4eb532f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateSubstitution
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordSubspaceIdeal_singleton
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordBlowupSubstMap_appTop_coord_self
import Theorems.Thm_P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop_bf5846d67e16db07


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
theorem _root_.solution (k : Type u) [Field k] (m : ℕ)
    (S : Finset (Fin m)) (s : Fin m) :
    (coordSubspaceIdeal k m {s}).comap (coordBlowupSubstMap k m S s) = coordSubspaceIdeal k m {s} := by
  rw [coordSubspaceIdeal_singleton, Scheme.IdealSheafData.comap_ofIdealTop,
    Ideal.map_span, Set.image_singleton, coordBlowupSubstMap_appTop_coord_self k m S s]
end FunctorialResolution.EmbeddedResolution
