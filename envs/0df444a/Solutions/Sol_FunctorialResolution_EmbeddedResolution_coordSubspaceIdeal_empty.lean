-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.coordSubspaceIdeal_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:25:17.347002+00:00
-- url     : https://prove2.me/submissions/4d230c1e-4253-46b5-b544-817accefb2a4

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateSubstitution
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordSubspaceIdeal_eq_ofIdealTop_span_coord


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
theorem _root_.solution (k : Type u) [Field k] (m : ℕ) :
    coordSubspaceIdeal k m (∅ : Finset (Fin m)) = ⊥ := by
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord]
  simp only [Finset.coe_empty, Set.image_empty, Ideal.span_empty]
  ext U
  simp [Ideal.map_bot]
end FunctorialResolution.EmbeddedResolution
