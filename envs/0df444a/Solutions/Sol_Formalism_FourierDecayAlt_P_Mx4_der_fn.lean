-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.der_fn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:25.240393+00:00
-- url     : https://prove2.me/submissions/e4cce032-6284-4e55-a61b-a76ea53cdd8f

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_eulerMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_mulOp_mul

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
theorem _root_.solution (a b : Fn r) (v w : Var r) (f fb : Fn r) :
    mk (mulOp a * euler v) (-(mulOp b * euler w)) * fnP f fb =
      fnP f fb * mk (mulOp a * euler v) (-(mulOp b * euler w)) + fnP (a * euler v f) (b * euler w fb) := by
  refine Prod.ext ?_ ?_
  · show mulOp a * euler v * mulOp f = mulOp f * (mulOp a * euler v) + mulOp (a * euler v f)
    rw [mul_assoc, eulerMul, mul_add, ← mul_assoc, ← mul_assoc, mulOp_mul, mulOp_mul, mulOp_mul, mul_comm a f]
  · show MulOpposite.op (mulOp fb * -(mulOp b * euler w)) =
      MulOpposite.op (-(mulOp b * euler w) * mulOp fb + mulOp (b * euler w fb))
    congr 1
    rw [neg_mul, mul_assoc, eulerMul, mul_add, ← mul_assoc, mulOp_mul, mulOp_mul, mul_neg, ← mul_assoc, mulOp_mul,
      mul_comm b fb]
    abel
end Formalism.FourierDecayAlt.P.Mx4
