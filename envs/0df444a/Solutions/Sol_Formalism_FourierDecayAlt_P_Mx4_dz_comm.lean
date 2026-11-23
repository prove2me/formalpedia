-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.dz_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:38.398088+00:00
-- url     : https://prove2.me/submissions/e5395a2e-7315-4806-8e3c-85f14f80749d

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_mk_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_dd_comm

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
theorem _root_.solution : (dzbP : Pr r) * dzP = dzP * dzbP := by
  apply mk_comm
  · exact dd_comm
  · rw [neg_mul_neg, neg_mul_neg]; exact dd_comm.symm
end Formalism.FourierDecayAlt.P.Mx4
