-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dual_measure_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:48:34.651179+00:00
-- url     : https://prove2.me/submissions/7b217ee0-f152-45cd-929b-54f61aa25d03

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Lemmata_FiberEquations_FiberEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualCovolumeChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx3_t_DualMeasureBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Module
open scoped ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.DualMeasureBound := Jx3.t_DualMeasureBound
end Formalism.FourierDecayAlt.P
