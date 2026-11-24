-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.lop_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:17.728782+00:00
-- url     : https://prove2.me/submissions/ed4882d8-aaa1-41f7-8cc9-58cc63071441

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_lop_apply

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
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (A B X : Module.End K W) (k : ℕ) : (lop A B ^ k) X = A ^ k * X * B ^ k := by
  induction k generalizing X with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, lop_apply, pow_succ A k, pow_succ' B k]
    simp only [mul_assoc]
end Formalism.InvariantFactorPaths.PW
