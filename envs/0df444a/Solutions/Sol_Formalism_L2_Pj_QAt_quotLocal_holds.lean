-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.quotLocal_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:28:54.950258+00:00
-- url     : https://prove2.me/submissions/0cbd87aa-cae7-4bc7-9bf2-1475754655a7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotSt
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_QuotLocalOfQuotientLength
import Theorems.Thm_Formalism_L2_Pj_QAt_quotLocal_of_quotientLength
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_quotientLength


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
namespace Formalism.L2.Pj.QAt
theorem _root_.solution : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotLocalStatement := by
  exact quotLocal_of_quotientLength Formalism.LatticeBaseChangeAlt.quotientLength
end Formalism.L2.Pj.QAt
