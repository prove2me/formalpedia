-- Prove2me | solution 1 for Formalism.RankGapBounds.WeightedMeanData.wmean_le_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:56:37.791101+00:00
-- url     : https://prove2.me/submissions/f6cd3c49-a852-4e52-85c7-4c8a9dd03554

import Definitions.Def_Formalism_RankGapBounds_MeanBoundSecondForm
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_wmean_mono
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_wmean_const

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
theorem _root_.solution [Nonempty ι] {d X : ι → ℝ} (hd : ∀ i, 0 < d i) (c : ℝ)
    (h : ∀ i, X i ≤ c) : wmean d X ≤ c := by
  have h1 := wmean_mono (X := X) (Y := fun _ => c) hd h
  have h3 := wmean_const hd c
  linarith
end Formalism.RankGapBounds.WeightedMeanData
