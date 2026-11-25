-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.conjugate_word_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:34:01.341192+00:00
-- url     : https://prove2.me/submissions/2ef738c7-5a87-4511-9737-de86e55a6aee

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_cwEigen_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_tTFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_exchange_plus_factor
import Theorems.Thm_Formalism_FourierDecayAlt_P_exchange_second_case
import Theorems.Thm_Formalism_FourierDecayAlt_P_negative_word_fixed
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
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.CwEigen := Formalism.FourierDecayAlt.P.Wd8.cwEigen_of Formalism.FourierDecayAlt.P.exchange_plus_factor Formalism.FourierDecayAlt.P.exchange_second_case
  Formalism.FourierDecayAlt.P.positive_word_fixed Formalism.FourierDecayAlt.P.negative_word_fixed Formalism.FourierDecayAlt.P.Wd8.tTFactor
end Formalism.FourierDecayAlt.P
