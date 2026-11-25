-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.exchange_vector_positive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:43:20.283461+00:00
-- url     : https://prove2.me/submissions/f0aec7f9-91d6-4d59-945b-db30a4949049

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_exchVecA_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_exchange_plus_factor
import Theorems.Thm_Formalism_FourierDecayAlt_P_positive_word_fixed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.ExchVecA := Formalism.FourierDecayAlt.P.Wd8.exchVecA_of Formalism.FourierDecayAlt.P.exchange_plus_factor Formalism.FourierDecayAlt.P.positive_word_fixed
end Formalism.FourierDecayAlt.P
