-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.admDK_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:34:21.873882+00:00
-- url     : https://prove2.me/submissions/01c14f25-deb3-49d3-ba72-f7c3a1680d0e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealWeightedForms
import Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_admissible_dual_kernel_identity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.FormPairingAction.AdmDK := Formalism.FourierDecayAlt.P.RealWeightedForms.admissible_dual_kernel_identity
end Formalism.FourierDecayAlt.P
