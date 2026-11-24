-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.coordSubspaceIdeal_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:53.644449+00:00
-- url     : https://prove2.me/submissions/145dede2-0bb2-4cde-9f56-cb0d833d41ce

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
theorem _root_.solution (k : Type u) [Field k] (m : ℕ) (j : Fin m) :
    coordSubspaceIdeal k m {j} =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)}) := by
  have h : ((fun i : Fin m => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ''
      (({j} : Finset (Fin m)) : Set (Fin m))) =
      {AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)} := by
    rw [Finset.coe_singleton, Set.image_singleton]
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord, h]
end FunctorialResolution.EmbeddedResolution
