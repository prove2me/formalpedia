-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:52.660102+00:00
-- url     : https://prove2.me/submissions/08597433-9f6c-4162-a05b-62e2b878b175

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleChart
theorem _root_.solution {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) {m : ℕ}
    (v : ULift.{u} (Fin m) → U.toScheme.presheaf.obj (op ⊤))
    (he : AlgebraicGeometry.Etale (AffineSpace.homOfVector (U.ι ≫ p) v)) :
    (EtaleChart.ofCoords p U v he).map = AffineSpace.homOfVector (U.ι ≫ p) v := rfl
end EtaleChart
end FunctorialResolution.EmbeddedResolution
