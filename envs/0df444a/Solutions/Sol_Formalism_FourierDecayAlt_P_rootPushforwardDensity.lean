-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.rootPushforwardDensity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:53:04.766552+00:00
-- url     : https://prove2.me/submissions/467ceb92-a96b-4fd0-9467-6e1f78c75c5c

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_densityChange_ok

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Polynomial
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.crystallineComparison.DensityChange :=
  Formalism.FourierDecayAlt.P.NthRootMeasurability.densityChange_ok
end Formalism.FourierDecayAlt.P
