-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.coordBlowupSubstMap_appTop_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:11:48.728555+00:00
-- url     : https://prove2.me/submissions/6040259d-e720-42f7-b962-c21067ce9cbb

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateSubstitution

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
theorem _root_.solution (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m)
    (i : ULift.{u} (Fin m)) :
    (coordBlowupSubstMap k m S s).appTop.hom (AffineSpace.coord (Spec (CommRingCat.of k)) i) =
      if i.down ∈ S ∧ i.down ≠ s then
        AffineSpace.coord (Spec (CommRingCat.of k)) i *
          AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s)
      else AffineSpace.coord (Spec (CommRingCat.of k)) i := by
  exact AffineSpace.homOfVector_appTop_coord ..
end FunctorialResolution.EmbeddedResolution
