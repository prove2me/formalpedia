-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.exchange_vector_negative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:43:14.297946+00:00
-- url     : https://prove2.me/submissions/94395f20-c2b6-4266-a267-f2596d9791d8

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_exchVecB_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_exchange_second_case
import Theorems.Thm_Formalism_FourierDecayAlt_P_negative_word_fixed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.ExchVecB := Formalism.FourierDecayAlt.P.Wd8.exchVecB_of Formalism.FourierDecayAlt.P.exchange_second_case Formalism.FourierDecayAlt.P.negative_word_fixed
end Formalism.FourierDecayAlt.P
