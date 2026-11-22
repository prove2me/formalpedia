-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.up_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:34.307209+00:00
-- url     : https://prove2.me/submissions/1ecca8ec-c3e9-4050-86ff-93bff4b11ea8

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
theorem _root_.solution (P : Par) (l : ℕ) (π π1 π2 : Ty P) (h1 : Up P l π1 π) (h2 : Up P l π2 π) : π1 = π2 := by
  funext i; apply Fin.ext
  exact Nat.add_right_cancel ((h1 i).symm.trans (h2 i))
end Formalism.FourierDecayAlt.P.Mx4
