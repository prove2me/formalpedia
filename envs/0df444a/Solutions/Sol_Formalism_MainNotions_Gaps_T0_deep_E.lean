-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.deep_E
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:20:38.319093+00:00
-- url     : https://prove2.me/submissions/86dc9575-49a5-4953-af42-46d88957bbbb

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
theorem _root_.solution {ld ln lr Pd PO : ℝ} (hPd : 0 ≤ Pd) (h1 : ld ≤ Pd) (h2 : ln ≤ PO) (h3 : lr ≤ PO) :
    ld + 1 / 2 * ln + lr ≤ 3 / 2 * (Pd + PO) := by linarith
end Formalism.MainNotions.Gaps.T0
