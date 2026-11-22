-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx3.val_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:06:03.185974+00:00
-- url     : https://prove2.me/submissions/5a7fad4d-5927-4ed3-b32f-fd6510ff86a4

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx3
namespace Formalism.FourierDecayAlt.P.Mx3
theorem _root_.solution (P : Par) (π : Ty P) (a b : Fin (P.k - 1)) (h : a = b) :
    ((π a : Fin _) : ℕ) = ((π b : Fin _) : ℕ) := by subst h; rfl
end Formalism.FourierDecayAlt.P.Mx3
