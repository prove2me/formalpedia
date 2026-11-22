-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.vz_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:06:15.843431+00:00
-- url     : https://prove2.me/submissions/9e330534-1e9e-4153-898d-5d945e087253

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
theorem _root_.solution : (vz : Var r) ≠ vzb := by
  intro h; have := congrArg (fun p : Var r => (ofLex p).2) h; simp [vz, vzb] at this
end Formalism.FourierDecayAlt.P.Mx4
