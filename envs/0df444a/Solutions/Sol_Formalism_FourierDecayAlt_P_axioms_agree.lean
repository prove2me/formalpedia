-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.axioms_agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:35:13.64223+00:00
-- url     : https://prove2.me/submissions/f0dc4dfd-d542-47be-896e-8487b0ed6ea5

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsdFormConjRewrite
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_t_AxiomsAgree

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
theorem _root_.solution : Formalism.FourierDecayAlt.J.AxiomsAgree := Jx1.t_AxiomsAgree
end Formalism.FourierDecayAlt.P
