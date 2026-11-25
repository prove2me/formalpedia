-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isSmoothDivisor_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:09:32.630151+00:00
-- url     : https://prove2.me/submissions/6ae34bf1-2c8e-4013-a0aa-ff3e2e34341a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsWithoutUnitIdeals
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_HasStrictNormalCrossingsWith_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_InStrictNormalCrossingPositionAt_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isSmoothDivisor_of_locally_coordIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] :
    IsSmoothDivisor p (⊤ : X.IdealSheafData) := by
  refine isSmoothDivisor_of_locally_coordIdeal (p := p) ⊤ ?_
  intro x
  obtain ⟨U, m, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p x
  exact ⟨U, hxU, m, c, Or.inl (Scheme.IdealSheafData.comap_top U.ι)⟩
end FunctorialResolution.EmbeddedResolution
