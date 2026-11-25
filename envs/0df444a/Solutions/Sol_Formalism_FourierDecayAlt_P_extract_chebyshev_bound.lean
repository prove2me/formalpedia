-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.extract_chebyshev_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:48:15.371961+00:00
-- url     : https://prove2.me/submissions/81836fda-b6ad-454f-8b3c-62ed6e16a64d

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LagrangeExtraction
import Theorems.Thm_Formalism_FourierDecayAlt_P_LagrangeExtraction_extractCheb

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
theorem _root_.solution : Formalism.FourierDecayAlt.F7.ExtractCheb := LagrangeExtraction.extractCheb
end Formalism.FourierDecayAlt.P
