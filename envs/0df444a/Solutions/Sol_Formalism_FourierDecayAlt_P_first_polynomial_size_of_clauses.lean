-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.first_polynomial_size_of_clauses
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:49:15.169915+00:00
-- url     : https://prove2.me/submissions/50ade6d8-64f1-47e9-ba70-8becb0c85f10

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealWeightedForms
import Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_first_polynomial_size_of_parts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.FormPairingAction.SizeBoundOfParts := Formalism.FourierDecayAlt.P.RealWeightedForms.first_polynomial_size_of_parts
end Formalism.FourierDecayAlt.P
