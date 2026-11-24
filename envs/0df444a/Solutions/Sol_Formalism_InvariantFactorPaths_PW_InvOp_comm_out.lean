-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.InvOp_comm_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:49:48.816298+00:00
-- url     : https://prove2.me/submissions/0928d168-411f-4af6-aa41-85d4633c2545

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Om_comm_out
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Pstep_comm

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
theorem _root_.solution (h : GlRel E) (l : ℕ) (c : ι) (L : List ι) (hc : c ∉ L) :
    E c c * InvOp E l L = InvOp E l L * E c c := by
  induction L with
  | nil => simp [InvOp]
  | cons z L ih =>
    have hcz : c ≠ z := by rintro rfl; exact hc (by simp)
    have hcL : c ∉ L := fun m => hc (by simp [m])
    have hP := Pstep_comm (E := E) L.toFinset z l (E c c)
      (fun q => Om_comm_out h (by simpa using hcL) (Ne.symm hcz) q)
    simp only [InvOp]
    rw [← mul_assoc, hP, mul_assoc, ih hcL, ← mul_assoc]
end Formalism.InvariantFactorPaths.PW
