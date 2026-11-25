-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.chebyshev_bound_attained
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:37:00.664287+00:00
-- url     : https://prove2.me/submissions/276d2c12-9a53-425e-9ea0-ea56285d9830

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_attained

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.F7.ChebAttained := ChebyshevExtremalPolynomials.attained
end Formalism.FourierDecayAlt.P
