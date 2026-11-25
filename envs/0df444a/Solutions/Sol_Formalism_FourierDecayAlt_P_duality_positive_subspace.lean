-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.duality_positive_subspace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:05:27.383114+00:00
-- url     : https://prove2.me/submissions/4815f194-5151-44ca-9e0d-36886c299342

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictedDualKernel
import Theorems.Thm_Formalism_FourierDecayAlt_P_RestrictedDualKernel_d1cSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.FormPairingAction.DualityPositiveSubspace := Formalism.FourierDecayAlt.P.RestrictedDualKernel.d1cSub
end Formalism.FourierDecayAlt.P
