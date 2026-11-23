-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.comm_eu
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:30.185833+00:00
-- url     : https://prove2.me/submissions/5d027374-f097-4324-9b04-bb2b056c87a1

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_eulerMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_eulerComm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_mulOp_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution (v w : Var r) (f : Fn r) (h : euler v f = 0) :
    euler v * (mulOp f * euler w) = (mulOp f * euler w) * euler v := by
  rw [← mul_assoc, eulerMul, h, mulOp_zero, add_zero, mul_assoc, mul_assoc, eulerComm]
end Formalism.FourierDecayAlt.P.Mx4
