-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.coordBlowupSubstMap_appTop_coord_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:17.356892+00:00
-- url     : https://prove2.me/submissions/dc8ffb46-c634-46e7-99ed-f0047720beaa

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateSubstitution
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordBlowupSubstMap_appTop_coord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordBlowupSubstMap_appTop_coord

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))
    (s : Fin m) (j : Fin m) (hj : j ∉ S) :
    (coordBlowupSubstMap k m S s).appTop.hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)) =
      AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j) := by
  have hc : ¬ ((ULift.up j : ULift.{u} (Fin m)).down ∈ S ∧
      (ULift.up j : ULift.{u} (Fin m)).down ≠ s) := fun h => hj h.1
  rw [coordBlowupSubstMap_appTop_coord k m S s (ULift.up j : ULift.{u} (Fin m)), if_neg hc]
end FunctorialResolution.EmbeddedResolution
