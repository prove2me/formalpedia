-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.poisson_level_decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:50:40.965642+00:00
-- url     : https://prove2.me/submissions/99c7b055-35f4-4705-a249-9d13cd7d5649

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay
import Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_poissonStep
import Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_stepDecay

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
theorem _root_.solution : Formalism.FourierDecayAlt.F7.PoissonStepDecay :=
  PoissonSummationDecay.stepDecay PoissonSummationDecay.poissonStep
end Formalism.FourierDecayAlt.P
