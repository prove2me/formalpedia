-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.R_matrix_UU_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:35:25.407808+00:00
-- url     : https://prove2.me/submissions/b8861691-f8f2-4c78-8eaa-3bbd90c015a1

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_rhUU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.RhUU := by
  intro K A S _ _ _ _ _ _ _ _ a D s
  exact Wd11.rhUU a D s
end Formalism.FourierDecayAlt.P
