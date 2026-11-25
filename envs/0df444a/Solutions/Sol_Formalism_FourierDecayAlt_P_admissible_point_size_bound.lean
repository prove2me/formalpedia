-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.admissible_point_size_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:34:25.144324+00:00
-- url     : https://prove2.me/submissions/8bf637ab-ad98-4740-862b-90bc5cfad41e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealWeightedForms
import Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_first_polynomial_size

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.FormPairingAction.AdmissiblePointSizeBound := Formalism.FourierDecayAlt.P.RealWeightedForms.first_polynomial_size
end Formalism.FourierDecayAlt.P
