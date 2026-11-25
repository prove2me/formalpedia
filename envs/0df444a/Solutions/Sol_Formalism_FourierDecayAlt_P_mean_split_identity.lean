-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.mean_split_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:50:21.00497+00:00
-- url     : https://prove2.me/submissions/0ea5cf78-04e6-42c7-a2a9-8f49bb892a48

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MiddleThirdEstimate
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanBoundsLimits
import Theorems.Thm_Formalism_FourierDecayAlt_P_MeanBoundsLimits_meanSplit_ok

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.crystallineComparison.MeanSplit := Formalism.FourierDecayAlt.P.MeanBoundsLimits.meanSplit_ok
end Formalism.FourierDecayAlt.P
