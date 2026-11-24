-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.graphJacobianMinorMatrix_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:27.197206+00:00
-- url     : https://prove2.me/submissions/072618cb-bd9a-4359-84b9-5ec996fa17e9

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
theorem _root_.solution (f : τ → MvPolynomial σ R) (v : τ → σ) (i j : τ) :
    graphJacobianMinorMatrix f v i j = MvPolynomial.pderiv (v i) (f j) :=
  rfl
end FunctorialResolution.EmbeddedResolution
