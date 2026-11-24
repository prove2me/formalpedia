-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.reducedInverseImage_eq_radical
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:50.138897+00:00
-- url     : https://prove2.me/submissions/ef89c99d-c009-47bd-a1b3-100553f5649d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsOpenImmersion
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_reducedInverseImage_eq_vanishingIdeal_closedPreimage

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
theorem _root_.solution {T Y : Scheme.{u}} (f : T ⟶ Y)
    (W : TopologicalSpace.Closeds Y) (J : T.IdealSheafData)
    (hJ : (J.support : Set T) = f.base ⁻¹' (W : Set Y)) :
    reducedInverseImage f W = J.radical := by
  have h : J.support = closedPreimage f W := SetLike.ext' hJ
  rw [reducedInverseImage_eq_vanishingIdeal_closedPreimage, ← h,
    Scheme.IdealSheafData.vanishingIdeal_support]
end FunctorialResolution.EmbeddedResolution
