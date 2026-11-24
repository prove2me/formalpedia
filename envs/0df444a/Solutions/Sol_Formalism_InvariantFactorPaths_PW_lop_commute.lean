-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.lop_commute
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:17.734321+00:00
-- url     : https://prove2.me/submissions/868af6d3-2402-4089-b7f8-b8f3280a8c7b

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
theorem _root_.solution {A B A' B' : Module.End K W} (hA : Commute A A') (hB : Commute B B') :
    Commute (lop A B) (lop A' B') := by
  show lop A B * lop A' B' = lop A' B' * lop A B
  refine LinearMap.ext fun X => ?_
  simp only [Module.End.mul_apply, lop_apply]
  have e1 : A * (A' * X * B') * B = (A * A') * X * (B' * B) := by simp only [mul_assoc]
  have e2 : A' * (A * X * B) * B' = (A' * A) * X * (B * B') := by simp only [mul_assoc]
  rw [e1, e2, hA.eq, hB.eq]
end Formalism.InvariantFactorPaths.PW
