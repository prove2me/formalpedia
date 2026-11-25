-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.share_of_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:15:12.965321+00:00
-- url     : https://prove2.me/submissions/d34f6eaa-8297-42b9-bf39-c71db1292eab

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
theorem _root_.solution {ρ' d x : ℝ} (hd : 0 < d) (h : ρ' / d ≤ x) : ρ' ≤ d * x := by
  rw [div_le_iff₀ hd] at h
  linarith
end Formalism.MainNotions.Gaps.T0
