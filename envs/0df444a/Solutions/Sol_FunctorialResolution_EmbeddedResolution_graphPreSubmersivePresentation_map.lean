-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.graphPreSubmersivePresentation_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:01.38481+00:00
-- url     : https://prove2.me/submissions/a69e977b-06c9-4a04-ba47-ae82c3550cd9

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {R : Type u} [CommRing R] {σ τ : Type u}
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (f : τ → MvPolynomial σ R) (v : τ → σ)
    (hv : Function.Injective v) :
    (graphPreSubmersivePresentation f v hv).map = v :=
  rfl
end FunctorialResolution.EmbeddedResolution
