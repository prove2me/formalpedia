-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.coordBlowupSubstMap_appTop_coord_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:32.171965+00:00
-- url     : https://prove2.me/submissions/930db5d1-eb06-42fa-97a8-6960c0281bdf

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
    (s : Fin m) :
    (coordBlowupSubstMap k m S s).appTop.hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s)) =
      AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s) := by
  have hc : ¬ ((ULift.up s : ULift.{u} (Fin m)).down ∈ S ∧
      (ULift.up s : ULift.{u} (Fin m)).down ≠ s) := by
    rintro ⟨-, h⟩
    exact h rfl
  rw [coordBlowupSubstMap_appTop_coord k m S s (ULift.up s : ULift.{u} (Fin m)), if_neg hc]
end FunctorialResolution.EmbeddedResolution
