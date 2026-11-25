-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.joint_form_theorem_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:53:28.984509+00:00
-- url     : https://prove2.me/submissions/38813b26-ee3c-4338-885f-48b2846d9446

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_t_MainJointForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.MainJointForm := Jx7.t_MainJointForm
end Formalism.FourierDecayAlt.P
