-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.majorant_is_profinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:46:48.497429+00:00
-- url     : https://prove2.me/submissions/7ab1d1bc-955a-4230-aa70-4dd58236b2ec

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsdFormConjRewrite
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_t_MajIsProf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.MajIsProf := Jx1.t_MajIsProf
end Formalism.FourierDecayAlt.P
