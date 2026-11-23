-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.comm_eu
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:15.611631+00:00
-- url     : https://prove2.me/submissions/019a5cb3-ea79-4581-9741-529ed7fa580f

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_eulerMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_eulerComm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx2
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx2
theorem _root_.solution (v w : Var r) (f : Fn r) (h : euler v f = 0) :
    euler v * (mulOp f * euler w) = (mulOp f * euler w) * euler v := by
  have h0 : mulOp (0 : Fn r) = 0 := by ext h : 1; simp [mulOp]
  rw [← mul_assoc, eulerMul, h, h0, add_zero, mul_assoc, mul_assoc, eulerComm]
end Formalism.FourierDecayAlt.P.Mx2
