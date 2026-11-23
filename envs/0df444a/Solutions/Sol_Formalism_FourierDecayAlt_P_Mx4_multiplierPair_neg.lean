-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.multiplierPair_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:22.184673+00:00
-- url     : https://prove2.me/submissions/c12dfcbd-72a5-45e0-a079-4296fab8f322

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_multiplierPair_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_multiplierPair_zero

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
theorem _root_.solution (f fb : Fn r) : -fnP f fb = fnP (-f) (-fb) := by
  rw [neg_eq_iff_add_eq_zero, multiplierPair_add, add_neg_cancel, add_neg_cancel, multiplierPair_zero]
end Formalism.FourierDecayAlt.P.Mx4
