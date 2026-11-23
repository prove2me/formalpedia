-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.diag_comm_omega
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:56.209585+00:00
-- url     : https://prove2.me/submissions/6ea7e08f-7a99-43de-b2c2-44992cc71592

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_der3
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GlRel_sw

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
theorem _root_.solution (h : GlRel E) {S : Finset ι} {z : ι} (hz : z ∉ S)
    (q : ℕ) : E z z * Om E S z q = Om E S z q * E z z := by
  induction q with
  | zero => simp [Om]
  | succ q ih =>
    simp only [Om]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hiz : i ≠ z := fun e => hz (e ▸ hi)
    have ho : E z z * Om E S z q = Om E S z q * E z z + 0 := by rw [ih, add_zero]
    rw [der3 _ _ _ _ _ _ _ (h.sw z z z i) ho (h.sw z z i z)]
    simp [hiz, Ne.symm hiz]
end Formalism.InvariantFactorPaths.PW
