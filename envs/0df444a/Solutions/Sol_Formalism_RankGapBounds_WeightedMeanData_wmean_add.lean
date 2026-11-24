-- Prove2me | solution 1 for Formalism.RankGapBounds.WeightedMeanData.wmean_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:35:53.175256+00:00
-- url     : https://prove2.me/submissions/04cd3bac-e27a-4841-98dd-0c2fa08df24d

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
theorem _root_.solution (d X Y : ι → ℝ) : wmean d (fun i => X i + Y i) = wmean d X + wmean d Y := by
  simp only [wmean, mul_add, Finset.sum_add_distrib, add_div]
end Formalism.RankGapBounds.WeightedMeanData
