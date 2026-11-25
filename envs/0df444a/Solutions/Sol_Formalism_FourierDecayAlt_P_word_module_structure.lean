-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.word_module_structure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:57:13.015617+00:00
-- url     : https://prove2.me/submissions/06908768-d2cf-4526-9591-db1726828a34

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_wordModule_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_word_free_of_unused_positions
import Theorems.Thm_Formalism_FourierDecayAlt_P_initial_module_structure
import Theorems.Thm_Formalism_FourierDecayAlt_P_letter_module_minus
import Theorems.Thm_Formalism_FourierDecayAlt_P_letter_module_plus


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.Wd
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.WordModule := Formalism.FourierDecayAlt.P.Wd5.wordModule_of initial_module_structure letter_module_plus letter_module_minus
  word_free_of_unused_positions
end Formalism.FourierDecayAlt.P
