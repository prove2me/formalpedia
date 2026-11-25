-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.duality_list_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:03:57.461195+00:00
-- url     : https://prove2.me/submissions/c9165558-1f20-49aa-9828-821f773210c9

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_dualityList_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_duality_minus
import Theorems.Thm_Formalism_FourierDecayAlt_P_duality_plus
import Theorems.Thm_Formalism_FourierDecayAlt_P_position_insertion_free_compat
import Theorems.Thm_Formalism_FourierDecayAlt_P_position_insertion_star_compat
import Theorems.Thm_Formalism_FourierDecayAlt_P_word_free_of_unused_positions
import Theorems.Thm_Formalism_FourierDecayAlt_P_word_module_structure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.DualityList :=
  Formalism.FourierDecayAlt.P.Wd10.dualityList_of Formalism.FourierDecayAlt.P.position_insertion_free_compat Formalism.FourierDecayAlt.P.position_insertion_star_compat
    Formalism.FourierDecayAlt.P.word_free_of_unused_positions Formalism.FourierDecayAlt.P.word_module_structure Formalism.FourierDecayAlt.P.duality_plus
    Formalism.FourierDecayAlt.P.duality_minus
end Formalism.FourierDecayAlt.P
