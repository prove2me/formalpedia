-- Prove2me | solution 1 for Formalism.RankGapBounds.WeightedMeanData.umean_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:35:51.588537+00:00
-- url     : https://prove2.me/submissions/93c71ef3-ee22-48ed-9e2a-54fe31c3a3e9

import Definitions.Def_Formalism_RankGapBounds_MeanBoundSecondForm
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.WeightedMeanData
noncomputable section
variable {ι : Type} [Fintype ι]
namespace Formalism.RankGapBounds.WeightedMeanData
theorem _root_.solution (X Y : ι → ℝ) : umean (fun i => X i + Y i) = umean X + umean Y := by
  simp only [umean, Finset.sum_add_distrib, add_div]
end Formalism.RankGapBounds.WeightedMeanData
