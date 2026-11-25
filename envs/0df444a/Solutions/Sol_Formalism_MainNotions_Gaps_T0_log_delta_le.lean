-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.log_delta_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:14:59.098836+00:00
-- url     : https://prove2.me/submissions/562c874a-e5ac-48f1-a422-6a1f3c7ed4e4

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
theorem _root_.solution {R δ d Pd : ℝ} (hR : 1 ≤ R) (hδ : 0 < δ) (hRδ : R * δ ≤ d) (hd : Real.log d ≤ Pd) :
    Real.log δ ≤ Pd := by
  have hδd : δ ≤ d := by nlinarith
  exact (Real.log_le_log hδ hδd).trans hd
end Formalism.MainNotions.Gaps.T0
