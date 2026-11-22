-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.multiplierPair_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:15:18.00099+00:00
-- url     : https://prove2.me/submissions/c6697d19-116d-4a22-9a33-278a136fe3b2

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_multiplierPair_mul

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
theorem _root_.solution (f fb g gb : Fn r) : fnP f fb * fnP g gb = fnP g gb * fnP f fb := by
  rw [multiplierPair_mul, multiplierPair_mul, mul_comm f, mul_comm fb]
end Formalism.FourierDecayAlt.P.Mx4
