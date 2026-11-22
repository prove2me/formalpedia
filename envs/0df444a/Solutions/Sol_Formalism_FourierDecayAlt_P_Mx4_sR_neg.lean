-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.sR_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:45:55.255885+00:00
-- url     : https://prove2.me/submissions/365fcf59-37ea-48fe-9abc-4138259fcf9d

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
theorem _root_.solution {P : Par} {l : ℕ} {π π' : Ty P} (h : ¬ Up P l π π') : sR P l π' π = 0 := by
  unfold sR; rw [Matrix.of_apply, if_neg h]
end Formalism.FourierDecayAlt.P.Mx4
