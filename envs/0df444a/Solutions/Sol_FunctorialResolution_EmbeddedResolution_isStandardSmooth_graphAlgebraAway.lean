-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isStandardSmooth_graphAlgebraAway
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:50:59.974469+00:00
-- url     : https://prove2.me/submissions/2cffb174-481b-4cbe-8c61-4116ccb7f061

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebra
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebraStandardSmooth

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
theorem _root_.solution [Fintype τ] [DecidableEq τ] [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    Algebra.IsStandardSmooth (MvPolynomial τ R) (GraphAlgebraAway f v) := by
  constructor
  exact ⟨Unit ⊕ Fin (Fintype.card σ), Unit ⊕ Fin (Fintype.card τ), inferInstance, inferInstance,
    ⟨graphAlgebraAwaySubmersivePresentation f v hv⟩⟩
end FunctorialResolution.EmbeddedResolution
