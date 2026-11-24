-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.NonzeroOnComponents.comap_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:20:29.014649+00:00
-- url     : https://prove2.me/submissions/ba684ecd-e9fa-42da-8668-85e13d317674

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SupportFlatPullback
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_NonzeroOnComponents_comap_of_generalizingMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem generalizingMap_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Flat f] :
    GeneralizingMap (fun x : ↥X => f x) :=
  AlgebraicGeometry.Flat.generalizingMap f
namespace NonzeroOnComponents
end NonzeroOnComponents
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.NonzeroOnComponents
namespace FunctorialResolution.EmbeddedResolution.NonzeroOnComponents
theorem _root_.solution {X Y : Scheme.{u}} {I : Y.IdealSheafData}
    (hI : NonzeroOnComponents I) (f : X ⟶ Y) [AlgebraicGeometry.Flat f] :
    NonzeroOnComponents (I.comap f) :=
  hI.comap_of_generalizingMap f (generalizingMap_of_flat f)
end FunctorialResolution.EmbeddedResolution.NonzeroOnComponents
