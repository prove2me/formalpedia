-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lemma_s_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:08:39.831348+00:00
-- url     : https://prove2.me/submissions/63d293b5-5c5f-4cfd-b000-5d17398eff73

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinLeTruncatedExponential
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_lemmaSOfSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TBB.LemmaSOfSteps := Formalism.FourierDecayAlt.P.TBBx1.lemmaSOfSteps
end Formalism.FourierDecayAlt.P
