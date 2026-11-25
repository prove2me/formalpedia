-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dual_kernel_duality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:49:53.165395+00:00
-- url     : https://prove2.me/submissions/67b0940a-dbdc-430f-b708-18abbd750f33

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_dkDualOK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.FormPairingAction.DKDualOK := Formalism.FourierDecayAlt.P.DualKernelLemmas.dkDualOK
end Formalism.FourierDecayAlt.P
