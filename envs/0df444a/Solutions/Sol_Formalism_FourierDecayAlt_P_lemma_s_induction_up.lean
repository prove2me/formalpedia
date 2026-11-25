-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lemma_s_induction_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:59:28.188444+00:00
-- url     : https://prove2.me/submissions/40f5b620-8192-4df3-bdf9-6ee420286ed8

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinLeTruncatedExponential
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_stepUp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TBB.StepUp := Formalism.FourierDecayAlt.P.TBBx1.stepUp
end Formalism.FourierDecayAlt.P
