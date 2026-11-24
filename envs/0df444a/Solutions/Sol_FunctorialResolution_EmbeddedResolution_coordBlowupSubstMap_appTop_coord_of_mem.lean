-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.coordBlowupSubstMap_appTop_coord_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:32.080907+00:00
-- url     : https://prove2.me/submissions/882cbf00-1a7f-4f89-82d4-4ab7f00d07f2

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
    (s : Fin m) (j : Fin m) (hj : j ∈ S) (hjs : j ≠ s) :
    (coordBlowupSubstMap k m S s).appTop.hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)) =
      AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j) *
        AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s) := by
  have hc : (ULift.up j : ULift.{u} (Fin m)).down ∈ S ∧
      (ULift.up j : ULift.{u} (Fin m)).down ≠ s := ⟨hj, hjs⟩
  rw [coordBlowupSubstMap_appTop_coord k m S s (ULift.up j : ULift.{u} (Fin m)), if_pos hc]
end FunctorialResolution.EmbeddedResolution
