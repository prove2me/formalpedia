-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.multiplierPair_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:22.650558+00:00
-- url     : https://prove2.me/submissions/5f46507c-d8ed-475e-8d64-f7bd006a2287

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
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
theorem _root_.solution : (fnP 0 0 : Pr r) = 0 := by
  refine Prod.ext mulOp_zero ?_
  show MulOpposite.op (mulOp (0 : Fn r)) = 0
  rw [mulOp_zero]; rfl
end Formalism.FourierDecayAlt.P.Mx4
