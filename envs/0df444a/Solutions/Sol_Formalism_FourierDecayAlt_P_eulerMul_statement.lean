-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.eulerMul_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:47:56.712144+00:00
-- url     : https://prove2.me/submissions/4077ce8c-9daa-4aac-90a8-af4e0619338c

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Theorems.Thm_Formalism_FourierDecayAlt_P_euler_leibniz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Mx1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.M.EulerMul := by
  intro r v f
  refine LinearMap.ext fun g => ?_
  simp only [Module.End.mul_apply, LinearMap.add_apply, mulOp, LinearMap.mulLeft_apply]
  rw [euler_leibniz r v f g, add_comm]
end Formalism.FourierDecayAlt.P
