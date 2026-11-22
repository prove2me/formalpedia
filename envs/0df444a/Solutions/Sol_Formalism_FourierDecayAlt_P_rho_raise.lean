-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.rho_raise
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:36.264822+00:00
-- url     : https://prove2.me/submissions/4674818e-6fbb-496c-94be-b92c5bfc641b

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_rhoUp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.M.RhoUp := Mx3.rhoUp
end Formalism.FourierDecayAlt.P
