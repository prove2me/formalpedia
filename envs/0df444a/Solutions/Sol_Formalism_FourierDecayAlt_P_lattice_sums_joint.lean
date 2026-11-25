-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lattice_sums_joint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:48:30.244422+00:00
-- url     : https://prove2.me/submissions/dace5c1f-ff57-48ff-a762-8521584132d2

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx2_t_LatticeSumsJoint

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
theorem _root_.solution : Formalism.FourierDecayAlt.J.LatticeSumsJoint := Jx2.t_LatticeSumsJoint
end Formalism.FourierDecayAlt.P
