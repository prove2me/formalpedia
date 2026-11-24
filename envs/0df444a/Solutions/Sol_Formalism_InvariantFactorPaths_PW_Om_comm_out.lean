-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Om_comm_out
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:48.409541+00:00
-- url     : https://prove2.me/submissions/cdcad031-6602-4dde-9391-0b60615fe19e

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_der3
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_diag_comm

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
theorem _root_.solution (h : GlRel E) {S : Finset ι} {z c : ι} (hc : c ∉ S) (hcz : z ≠ c)
    (q : ℕ) : E c c * Om E S z q = Om E S z q * E c c := by
  induction q with
  | zero => simp [Om]
  | succ q ih =>
    simp only [Om]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hic : i ≠ c := fun e => hc (e ▸ hi)
    have ho : E c c * Om E S z q = Om E S z q * E c c + 0 := by rw [ih, add_zero]
    have hf : E c c * E z i = E z i * E c c + 0 := by rw [diag_comm h hcz hic, add_zero]
    have he : E c c * E i z = E i z * E c c + 0 := by rw [diag_comm h hic hcz, add_zero]
    rw [der3 _ _ _ _ _ _ _ hf ho he]
    simp
end Formalism.InvariantFactorPaths.PW
