-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.deep_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:20:53.944612+00:00
-- url     : https://prove2.me/submissions/7ec73121-3e0c-4be8-8de3-517b8631b67a

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
theorem _root_.solution {κ F' F0 T D L : ℝ} (h : κ = F' + T * L - T) (h0 : F0 = F' + D * L - D) :
    (T - D) * L + F0 = κ + T - D := by linear_combination h0 - h
end Formalism.MainNotions.Gaps.T0
