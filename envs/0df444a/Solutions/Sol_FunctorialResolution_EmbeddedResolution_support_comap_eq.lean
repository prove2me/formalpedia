-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.support_comap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:44.469185+00:00
-- url     : https://prove2.me/submissions/a20d4d6b-5d53-4153-874b-874ce724fe28

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X Y : Scheme} (f : X ⟶ Y) (I : Y.IdealSheafData) :
    ((I.comap f).support : Set X) = f.base ⁻¹' (I.support : Set Y) :=
  congrArg (fun s : TopologicalSpace.Closeds X => (s : Set X))
    (Scheme.IdealSheafData.support_comap I f)
end FunctorialResolution.EmbeddedResolution
