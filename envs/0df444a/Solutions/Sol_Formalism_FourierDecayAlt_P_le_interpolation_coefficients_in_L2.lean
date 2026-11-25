-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.le_interpolation_coefficients_in_L2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:51:34.2651+00:00
-- url     : https://prove2.me/submissions/f438d714-1c79-47e3-a436-d90425bd9fd0

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivedCoefficientIntegrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_coefficient_L2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.LE.InterpolationCoefficientsInL2 :=
  Formalism.FourierDecayAlt.P.LEx2.coefficient_L2
end Formalism.FourierDecayAlt.P
