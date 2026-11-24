-- Prove2me | solution 1 for Formalism.ThetaLiftIndependence.ChainScalarLemmas.mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:46:00.888653+00:00
-- url     : https://prove2.me/submissions/159cef07-66fd-4372-88e8-8fd4b08096e3

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ChainScalar
import Theorems.Thm_Formalism_ThetaLiftIndependence_ChainScalarLemmas_adjoint_downChain_succ_apply

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
theorem _root_.solution (T : ∀ j, E (j + 1) →ₗ[𝕜] E j) (S : ∀ j, Submodule 𝕜 (E j))
    (hS : ∀ j, ∀ x ∈ S j, LinearMap.adjoint (T j) x ∈ S (j + 1)) :
    ∀ (m : ℕ), ∀ x ∈ S 0, LinearMap.adjoint (downChain T m) x ∈ S m := by
  intro m
  induction m with
  | zero =>
    intro x hx
    show LinearMap.adjoint (LinearMap.id : E 0 →ₗ[𝕜] E 0) x ∈ S 0
    rw [LinearMap.adjoint_id]
    exact hx
  | succ m ih =>
    intro x hx
    rw [adjoint_downChain_succ_apply]
    exact hS m _ (ih x hx)
end Formalism.ThetaLiftIndependence.ChainScalarLemmas
