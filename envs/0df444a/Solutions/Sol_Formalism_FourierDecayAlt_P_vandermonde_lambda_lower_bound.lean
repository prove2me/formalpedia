-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.vandermonde_lambda_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:02:32.987156+00:00
-- url     : https://prove2.me/submissions/9cfeff9b-ea14-42c3-b5f6-235a2cbc46c4

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_vandLamLower

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
theorem _root_.solution : Formalism.FourierDecayAlt.Sz.VandLamLower := Sz5.vandLamLower
end Formalism.FourierDecayAlt.P
