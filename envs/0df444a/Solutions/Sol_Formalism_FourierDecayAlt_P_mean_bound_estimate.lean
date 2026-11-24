-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.mean_bound_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:54.657716+00:00
-- url     : https://prove2.me/submissions/c75a5c36-f0c7-4249-bb06-a23e563bec25

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MiddleThirdEstimate
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanBoundsLimits
import Theorems.Thm_Formalism_FourierDecayAlt_P_MeanBoundsLimits_meanBound_ok

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
theorem _root_.solution : Formalism.FourierDecayAlt.crystallineComparison.MeanBound := Formalism.FourierDecayAlt.P.MeanBoundsLimits.meanBound_ok
end Formalism.FourierDecayAlt.P
