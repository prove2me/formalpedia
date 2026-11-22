-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.mulOp_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:06:15.514804+00:00
-- url     : https://prove2.me/submissions/ec940ed6-d36a-4d97-9d5b-bde95ca420a5

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
theorem _root_.solution (f g : Fn r) : mulOp f * mulOp g = mulOp (f * g) := by
  ext h : 1; simp [mulOp]
end Formalism.FourierDecayAlt.P.Mx4
