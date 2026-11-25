-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.extract_probability_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:48:21.214888+00:00
-- url     : https://prove2.me/submissions/243ce22f-f786-420a-9475-6bffe13932c1

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LagrangeExtraction
import Theorems.Thm_Formalism_FourierDecayAlt_P_LagrangeExtraction_extractProb

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
theorem _root_.solution : Formalism.FourierDecayAlt.F7.ExtractProb := LagrangeExtraction.extractProb
end Formalism.FourierDecayAlt.P
