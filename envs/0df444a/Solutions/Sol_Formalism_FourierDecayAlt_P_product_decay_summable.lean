-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.product_decay_summable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:47:28.493401+00:00
-- url     : https://prove2.me/submissions/7f7244c4-9f73-433b-acdf-1788370edefc

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay
import Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_productDecay

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
theorem _root_.solution : Formalism.FourierDecayAlt.F7.ProductDecaySummable := PoissonSummationDecay.productDecay
end Formalism.FourierDecayAlt.P
