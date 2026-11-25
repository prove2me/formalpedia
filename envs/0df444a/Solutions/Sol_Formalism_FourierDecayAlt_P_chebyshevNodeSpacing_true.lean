-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.chebyshevNodeSpacing_true
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:53:20.626875+00:00
-- url     : https://prove2.me/submissions/23e9d29d-0bf8-4fd1-a4d6-c4530d394dfb

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_spacing

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
theorem _root_.solution : Formalism.FourierDecayAlt.F7.ChebSpacing := ChebyshevExtremalPolynomials.spacing
end Formalism.FourierDecayAlt.P
