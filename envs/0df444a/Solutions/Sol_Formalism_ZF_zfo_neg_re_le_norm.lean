-- Prove2me | solution 1 for Formalism.ZF.zfo_neg_re_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:43:02.566045+00:00
-- url     : https://prove2.me/submissions/82f1dccb-e5cc-4771-93b0-6fa081cfab70

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZfoTermReNonneg
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZfoGrowthBall
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZfoNegReLeNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Metric
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution (x : ℂ) : (-x).re ≤ ‖x‖ := by
  rw [Complex.neg_re]
  exact (neg_le_abs x.re).trans (Complex.abs_re_le_norm x)
end Formalism.ZF
