-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lemma_s_induction_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:45:35.072616+00:00
-- url     : https://prove2.me/submissions/7d04ffed-ff00-4461-ac08-c3acc19a1ab0

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinLeTruncatedExponential
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_stepOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TBB.StepOne := Formalism.FourierDecayAlt.P.TBBx1.stepOne
end Formalism.FourierDecayAlt.P
