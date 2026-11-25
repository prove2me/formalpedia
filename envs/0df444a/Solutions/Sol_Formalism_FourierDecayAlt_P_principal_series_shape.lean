-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.principal_series_shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:51:41.527372+00:00
-- url     : https://prove2.me/submissions/63cd3df8-7b1c-4620-969a-479f3be11352

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_t_MainRowShape

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
theorem _root_.solution : Formalism.FourierDecayAlt.PB.MainRowShape := GrowthPolynomialOperator.t_MainRowShape
end Formalism.FourierDecayAlt.P
