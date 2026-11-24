-- Prove2me | solution 1 for Formalism.ThetaLiftIndependence.ChainScalarLemmas.adjoint_downChain_succ_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:37:08.349808+00:00
-- url     : https://prove2.me/submissions/cff321df-4193-4ad1-a06c-08e5d2b2af95

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ChainScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ThetaLiftIndependence
open Formalism.ThetaLiftIndependence.ChainScalarLemmas
variable {𝕜 : Type} [RCLike 𝕜] {E : ℕ → Type} [∀ j, NormedAddCommGroup (E j)]
    [∀ j, InnerProductSpace 𝕜 (E j)] [∀ j, FiniteDimensional 𝕜 (E j)]
namespace Formalism.ThetaLiftIndependence.ChainScalarLemmas
theorem _root_.solution (T : ∀ j, E (j + 1) →ₗ[𝕜] E j) (m : ℕ) (x : E 0) :
    LinearMap.adjoint (downChain T (m + 1)) x =
      LinearMap.adjoint (T m) (LinearMap.adjoint (downChain T m) x) := by
  show LinearMap.adjoint ((downChain T m).comp (T m)) x = _
  rw [LinearMap.adjoint_comp]
  rfl
end Formalism.ThetaLiftIndependence.ChainScalarLemmas
