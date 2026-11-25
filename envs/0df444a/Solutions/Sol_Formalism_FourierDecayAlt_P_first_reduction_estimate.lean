-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.first_reduction_estimate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:52:50.74629+00:00
-- url     : https://prove2.me/submissions/e2535ece-3e7c-4b00-9c07-fd43f39e588f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_dkStep1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.FormPairingAction.DKStep1 := Formalism.FourierDecayAlt.P.DualKernelLemmas.dkStep1
end Formalism.FourierDecayAlt.P
