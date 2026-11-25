-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.add_half_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:17:54.189969+00:00
-- url     : https://prove2.me/submissions/139527cf-7b85-418e-8503-4b9cf61fc61d

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QuotientParamNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0
namespace Formalism.MainNotions.Gaps.T0
theorem _root_.solution {lrw Prw L : ℝ} (h : lrw ≤ Prw * (L - 1)) (hP : 1 / 2 ≤ Prw) :
    lrw + 1 / 2 ≤ Prw * L := by linarith
end Formalism.MainNotions.Gaps.T0
