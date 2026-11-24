-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.invariant_natural_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:46.72939+00:00
-- url     : https://prove2.me/submissions/16887182-b506-4328-9b33-238f605668c8

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Pstep_nat

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
variable {K W W' ι : Type} [Field K] [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W'] [DecidableEq ι]
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution : InvNat := by
  intro K W W' ι _ _ _ _ _ _ E E' θ h l L
  induction L with
  | nil => intro x; simp [InvOp]
  | cons z L ih =>
    intro x
    simp only [InvOp, Module.End.mul_apply]
    rw [Pstep_nat E E' θ h, ih]
end Formalism.InvariantFactorPaths.PW
