-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.extractBound_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:48:06.163805+00:00
-- url     : https://prove2.me/submissions/e243a66b-756a-46c1-a6bd-e6b5cce75987

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LagrangeExtraction
import Theorems.Thm_Formalism_FourierDecayAlt_P_LagrangeExtraction_extractBound

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
theorem _root_.solution : Formalism.FourierDecayAlt.F7.ExtractBound := LagrangeExtraction.extractBound
end Formalism.FourierDecayAlt.P
