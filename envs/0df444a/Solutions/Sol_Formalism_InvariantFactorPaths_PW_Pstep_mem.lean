-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Pstep_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:41:38.998955+00:00
-- url     : https://prove2.me/submissions/458a5d7e-b07e-4fcb-8646-bfc92a85a4a3

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Om_mem

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
theorem _root_.solution {NN : Submodule K W} (hN : ∀ a b, ∀ x ∈ NN, E a b x ∈ NN) (S : Finset ι) (z : ι) (l : ℕ) :
    ∀ x ∈ NN, Pstep E S z l x ∈ NN := by
  intro x hx
  simp only [Pstep, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ (fun q _ => Submodule.smul_mem _ _ (Om_mem hN S z q x hx))
end Formalism.InvariantFactorPaths.PW
