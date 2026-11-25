-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.top_action_on_gauge_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:29:14.429681+00:00
-- url     : https://prove2.me/submissions/b72c8411-bed4-4491-902e-426fcc3106c1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTRTopActCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTRTopActAlg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTRTopAct
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_TopAct_gTRTopAct_of_cut
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_quadratic_top_algebra_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
theorem _root_.solution : GTRTopAct := TopAct.gTRTopAct_of_cut quadratic_top_algebra_holds
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
