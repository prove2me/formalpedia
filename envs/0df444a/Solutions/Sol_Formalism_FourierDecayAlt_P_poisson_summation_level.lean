-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.poisson_summation_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:48:30.602354+00:00
-- url     : https://prove2.me/submissions/0e7b955f-a748-4ca1-9bb9-9a1410ba4f23

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay
import Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_poissonStep

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
theorem _root_.solution : Formalism.FourierDecayAlt.F7.PoissonStep := PoissonSummationDecay.poissonStep
end Formalism.FourierDecayAlt.P
