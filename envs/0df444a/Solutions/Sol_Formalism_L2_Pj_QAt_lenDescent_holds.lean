-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.lenDescent_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:44:15.215591+00:00
-- url     : https://prove2.me/submissions/2083e2fb-988e-4c30-af0f-ec47b09ab49c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreSt
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthBaseChange
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_LenDescentOfLengthBaseChangeLocal
import Theorems.Thm_Formalism_L2_Pj_QAt_lenDescent_of_lengthBaseChangeLocal
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_lengthBaseChangeLocal


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
theorem _root_.solution : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LenDescentStatement :=
  lenDescent_of_lengthBaseChangeLocal Formalism.LatticeBaseChangeAlt.lengthBaseChangeLocal
end Formalism.L2.Pj.QAt
