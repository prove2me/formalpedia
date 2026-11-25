-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dual_kernel_lemma_restricted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:39:39.706888+00:00
-- url     : https://prove2.me/submissions/2e2d738a-4bab-4193-a695-2f7bd61b451e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictedDualKernel
import Theorems.Thm_Formalism_FourierDecayAlt_P_RestrictedDualKernel_lemmaDKSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.FormPairingAction.LemmaDKSub := Formalism.FourierDecayAlt.P.RestrictedDualKernel.lemmaDKSub
end Formalism.FourierDecayAlt.P
