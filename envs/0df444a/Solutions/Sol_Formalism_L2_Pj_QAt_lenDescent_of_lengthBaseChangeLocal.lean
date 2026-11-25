-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.lenDescent_of_lengthBaseChangeLocal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:29:47.729846+00:00
-- url     : https://prove2.me/submissions/66b03d2f-78eb-4186-812d-14e9982746a4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreSt
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthBaseChange
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_LenDescentOfLengthBaseChangeLocal
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLD_main_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
open TieLD
namespace Formalism.L2.Pj.QAt
theorem _root_.solution (h : Formalism.LatticeBaseChangeAlt.LengthBaseChangeLocal) :
    ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LenDescentStatement := by
  unfold ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LenDescentStatement
  intro K K₁ V _ _ _ _ _ _ _ _ _ _ M hMfg _ W ρ θ la w hw
  exact TieLD.main_eq h M hMfg W θ la w hw
end Formalism.L2.Pj.QAt
