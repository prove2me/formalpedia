-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.extract_K_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:48:11.559077+00:00
-- url     : https://prove2.me/submissions/351ed3b0-37f6-493b-a05e-85f9dd5e430a

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LagrangeExtraction
import Theorems.Thm_Formalism_FourierDecayAlt_P_LagrangeExtraction_extractK

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
theorem _root_.solution : Formalism.FourierDecayAlt.F7.ExtractK := LagrangeExtraction.extractK
end Formalism.FourierDecayAlt.P
