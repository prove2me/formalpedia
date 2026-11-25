-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.duality_cauchy_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:37:49.833539+00:00
-- url     : https://prove2.me/submissions/e863a83c-2eb8-4921-ba38-81e493127888

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_d1c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.FormPairingAction.DualityCauchySchwarz := Formalism.FourierDecayAlt.P.DualKernelLemmas.d1c
end Formalism.FourierDecayAlt.P
