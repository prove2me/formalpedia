-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.equioscillation_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:40:35.862291+00:00
-- url     : https://prove2.me/submissions/c00f00e0-4f3d-4e6b-98bc-976ec30f9937

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_equiCo

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
theorem _root_.solution : Formalism.FourierDecayAlt.F7.EquiCo := ChebyshevExtremalPolynomials.equiCo
end Formalism.FourierDecayAlt.P
