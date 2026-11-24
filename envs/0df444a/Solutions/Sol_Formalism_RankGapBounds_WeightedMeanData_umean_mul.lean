-- Prove2me | solution 1 for Formalism.RankGapBounds.WeightedMeanData.umean_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:35:52.286003+00:00
-- url     : https://prove2.me/submissions/e47998d0-0f21-4af1-a1eb-5b18bb5ef2d4

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
theorem _root_.solution (c : ℝ) (X : ι → ℝ) : umean (fun i => c * X i) = c * umean X := by
  simp only [umean, ← Finset.mul_sum, mul_div_assoc]
end Formalism.RankGapBounds.WeightedMeanData
