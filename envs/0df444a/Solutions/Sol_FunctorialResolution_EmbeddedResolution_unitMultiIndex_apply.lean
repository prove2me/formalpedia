-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.unitMultiIndex_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:48.208867+00:00
-- url     : https://prove2.me/submissions/d09f911d-579d-4b24-9e83-a88d9f384342

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_MultiIndexDerivation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {h : ℕ} (i j : Fin h) :
    unitMultiIndex i j = if j = i then 1 else 0 := rfl
end FunctorialResolution.EmbeddedResolution
