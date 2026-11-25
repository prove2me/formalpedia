-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.equioscillation_coeff_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:42:00.075985+00:00
-- url     : https://prove2.me/submissions/d311d98b-6827-4b41-a637-9bf3834125a2

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_equiCoBound

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
theorem _root_.solution : Formalism.FourierDecayAlt.F7.EquiCoBound := ChebyshevExtremalPolynomials.equiCoBound
end Formalism.FourierDecayAlt.P
