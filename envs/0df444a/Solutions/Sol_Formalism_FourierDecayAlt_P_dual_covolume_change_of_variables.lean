-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dual_covolume_change_of_variables
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:39:23.969056+00:00
-- url     : https://prove2.me/submissions/c4b18f3a-051c-4593-9acd-d9d40c8122a7

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Lemmata_FiberEquations_FiberEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualCovolumeChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx3_t_DualCovolumeCV

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
theorem _root_.solution : Formalism.FourierDecayAlt.J.DualCovolumeCV := Jx3.t_DualCovolumeCV
end Formalism.FourierDecayAlt.P
