-- Prove2me | solution 1 for Formalism.RankGapBounds.WeightedMeanData.sum_pos_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:35:50.790281+00:00
-- url     : https://prove2.me/submissions/628f7e0b-5422-4a0b-a427-2c17420dcd95

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
theorem _root_.solution [Nonempty ι] {d : ι → ℝ} (hd : ∀ i, 0 < d i) : 0 < ∑ i, d i :=
  Finset.sum_pos (fun i _ => hd i) Finset.univ_nonempty
end Formalism.RankGapBounds.WeightedMeanData
