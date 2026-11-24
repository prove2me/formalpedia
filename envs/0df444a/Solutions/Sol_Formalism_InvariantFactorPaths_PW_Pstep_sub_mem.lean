-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Pstep_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:16.704847+00:00
-- url     : https://prove2.me/submissions/ba4e8931-6563-4a7d-b201-516e5770210c

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_cc_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Pstep_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_range_mem

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
theorem _root_.solution [CharZero K] {S : Finset ι} {z : ι} (hz : z ∉ S) (l : ℕ) (u : W) :
    Pstep E S z l u - u ∈ ⨆ (a : ι) (b : ι) (_ : a ≠ b), LinearMap.range (E a b) := by
  rw [Pstep_eq, Finset.sum_range_succ']
  simp only [LinearMap.add_apply, cc_zero, one_smul, Om, Module.End.one_apply, add_sub_cancel_right,
    LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
  refine Submodule.sum_mem _ (fun q _ => Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun i hi => ?_)))
  exact range_mem (E := E) (show z ≠ i from fun e => hz (e ▸ hi)) _
end Formalism.InvariantFactorPaths.PW
