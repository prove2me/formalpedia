-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Om_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:40.24647+00:00
-- url     : https://prove2.me/submissions/0c260862-2e35-40cf-8787-26dbbe9c2467

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset
variable {K W ι : Type} [Field K] [AddCommGroup W] [Module K W] [DecidableEq ι]
variable {E : ι → ι → Module.End K W}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution {NN : Submodule K W} (hN : ∀ a b, ∀ x ∈ NN, E a b x ∈ NN) (S : Finset ι) (z : ι) (q : ℕ) :
    ∀ x ∈ NN, Om E S z q x ∈ NN := by
  induction q with
  | zero => intro x hx; simpa [Om] using hx
  | succ q ih =>
    intro x hx
    simp only [Om, LinearMap.sum_apply, Module.End.mul_apply]
    exact Submodule.sum_mem _ (fun i _ => hN _ _ _ (ih _ (hN _ _ _ hx)))
end Formalism.InvariantFactorPaths.PW
