-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.val_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:57:50.023019+00:00
-- url     : https://prove2.me/submissions/17968e43-d0d2-471f-97eb-95e1f6e7bba4

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
theorem _root_.solution (P : Par) (π : Ty P) (a b : Fin (P.k - 1)) (h : a = b) :
    ((π a : Fin _) : ℕ) = ((π b : Fin _) : ℕ) := by subst h; rfl
end Formalism.FourierDecayAlt.P.Mx4
