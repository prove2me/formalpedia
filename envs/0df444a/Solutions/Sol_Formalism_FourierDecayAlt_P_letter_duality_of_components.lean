-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.letter_duality_of_components
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:58:23.21871+00:00
-- url     : https://prove2.me/submissions/d12b65a9-2ce0-48c2-bb28-a7878a1a29a5

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_letter_duality_of_clauses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.FormPairingAction.LetterDualityOfParts := Formalism.FourierDecayAlt.P.DualKernelLemmas.letter_duality_of_clauses
end Formalism.FourierDecayAlt.P
