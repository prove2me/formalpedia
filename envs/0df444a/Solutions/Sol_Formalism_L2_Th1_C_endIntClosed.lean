-- Prove2me | solution 1 for Formalism.L2.Th1.C.endIntClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:55:27.659969+00:00
-- url     : https://prove2.me/submissions/f0daa929-c02c-4bd1-aa3f-e8c5527ff69a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_UnitaryInverseIdentity
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralEndomorphismFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Theorems.Thm_P2M_Formalism_L2_Th1_C_integralEndoClosed__c3bb72aeab08


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
namespace Formalism.L2.Th1.C
theorem _root_.solution : EndIntClosed := integralEndoClosed'
end Formalism.L2.Th1.C
