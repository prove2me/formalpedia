-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.mk_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:25.192287+00:00
-- url     : https://prove2.me/submissions/f9c0812f-2cf6-45ab-9c82-ccf2b3a5611a

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity

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
theorem _root_.solution (X Xs Y Ys : Op r) (h1 : X * Y = Y * X) (h2 : Xs * Ys = Ys * Xs) : mk X Xs * mk Y Ys = mk Y Ys * mk X Xs := by
  refine Prod.ext h1 ?_
  show MulOpposite.op (Ys * Xs) = MulOpposite.op (Xs * Ys)
  rw [h2]
end Formalism.FourierDecayAlt.P.Mx4
