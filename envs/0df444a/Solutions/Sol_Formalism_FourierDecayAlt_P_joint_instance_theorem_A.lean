-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.joint_instance_theorem_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:41:20.794247+00:00
-- url     : https://prove2.me/submissions/0242e286-0ec3-4325-8cf9-3618b4e9bb00

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_t_MainJointInst

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
theorem _root_.solution : Formalism.FourierDecayAlt.J.MainJointInst := Jx7.t_MainJointInst
end Formalism.FourierDecayAlt.P
