-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.word_free_of_unused_positions
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:51.824398+00:00
-- url     : https://prove2.me/submissions/6426e6d4-4839-42ef-8bf4-c05ae1348bcd

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_word_free

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
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.WordFree := by
  intro K A S _ _ _ _ _ _ _ _ QQ w c hc
  exact Formalism.FourierDecayAlt.P.Wd5.word_free QQ w c hc
end Formalism.FourierDecayAlt.P
